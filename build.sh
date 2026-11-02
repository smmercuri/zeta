#!/usr/bin/env bash
# Build the project with Lake's parallelism sized to this machine and to the certified height,
# optionally discarding or archiving each certificate batch's proof term as it is built.
#
#   ./build.sh                          # default target(s), auto-sized, proof terms kept
#   ./build.sh Zeta.Main                # any lake build targets
#   ./build.sh --proofs=discard         # replace each batch's proof term by a placeholder + hash
#   ./build.sh --proofs=archive         # ... by a lossless archive + hash
#   ./build.sh --native                 # the `Native` library instead: the same theorem with the
#                                       #   Riemann–Siegel batches checked by `native_decide`
#   ./build.sh --estimate [--native]    # build two sample batches (shards), measure them, and
#                                       #   project the whole build; later runs size from it
#   ./build.sh --retries K              # the kernel raises a failing row's precision up to K times
#                                       #   (default 3); `--native` says when that is too few
#   LEAN_NUM_THREADS=8 ./build.sh       # explicit override of the worker count
#
# Workers. Each certificate batch is a separate `lean` process. All of them map the same imported
# oleans (≈ SHARED_GB), so that part is paid once; what each extra worker costs is its *private*
# memory, which grows with the batch's rows times its Riemann–Siegel cutoff ν = ⌊√(t/2π)⌋ (each
# row's certificate holds main sums of ν terms). Peak private memory is modelled as
# BASE_GB + PER_ROW_NU_GB · rows · ν, which includes the proof term a build holds until
# `--proofs=discard` shrinks it. So
#
#   per-worker GB = BASE_GB + PER_ROW_NU_GB · load_max   (load_max: the largest batch's rows·ν)
#   workers       = min(cores, (available − SHARED_GB) / per-worker GB)
#
# unless LEAN_NUM_THREADS is already set, in which case that value is respected. The generator
# sizes batches to the same model (`batch_rows`, `BATCH_BASE_GB` and `BATCH_ROW_NU_GB` in
# `python/src/config.py`), so above height ≈ 2·10⁶ every batch's rows·ν is about the same and
# so is its memory; below, batches keep 200 rows and need less.
#
# Since the per-worker memory is smaller lower down, a count sized for the largest batch leaves
# cores idle there. So when the memory is what limits the count, a default build runs in stages
# up the height, each on as many workers as fit at its largest batch (see "Staging" below).
#
# "available" is what the machine can hand out *now*. On macOS that is `memory_pressure`'s free
# percentage of `hw.memsize` (it counts compressed and file-backed pages the kernel will reclaim),
# falling back to `vm_stat`'s free + inactive + speculative + purgeable pages, which undercounts;
# on Linux the kernel's own `MemAvailable`.
#
# Disk. A batch's proof term lives in its `.olean.private` and is by far the largest thing a build
# writes: ROW_KB + ROW_NU_KB·ν per row, about 1.3 GB in total at height 1e4, 42 GB at 1e5 and
# 1.5 TB at 1e6. Before building, the proof terms of the
# batches not yet built are estimated from their sources (`BatchSpec` records each batch's row
# count and endpoints) and compared with the free disk; if they would take a large share of it, a
# warning recommends `--proofs=discard`.
#
# Native. `--native` builds `Native.riemannHypothesisUpTo_10011` (`Native/Main.lean`): the
# Riemann–Siegel batches are checked by compiled evaluation, so the result
# also trusts the Lean compiler (`#print axioms` lists one `native_decide` axiom per batch), and it
# runs much faster than the kernel check. Regenerate its certificates with
# `python/src/data_gen/gen_native_certificates.py`. It first builds `Native.PluginCheck`, which
# fails if the checker would run in the interpreter. It also predicts
# the kernel-checked build: each native batch checks, from its own far more precise values, that
# every zero clears its error bound by more than the kernel's enclosures will be wide after the
# kernel's retries (3, or `--retries K`); zeros that do not are gathered into a banner at the end
# ("THE KERNEL-CHECKED BUILD WILL FAIL ON THESE ZEROS"), with the K that fixes them, exit status 3.
# On Linux it puts the toolchain's library directory on `LD_LIBRARY_PATH` (else loading the checker
# fails with "libLake_shared.so: cannot open shared object file"); a bare `lake build Native…`
# there needs
#   export LD_LIBRARY_PATH="$(lean --print-libdir)${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
#
# Estimate. `--estimate` builds two of the batches not yet built (with `--native`, two shards): the
# one with the highest mean ν and one near the median, plus an import-only probe module beside them.
# Lake builds each once, which also records the exact `lean` invocation; that `lean` process alone
# is then re-run and measured (CPU and wall time, peak RSS by `getrusage`), so Lake's own work is
# not in the numbers, and the import's cost is subtracted; for kernel batches it also reads the
# `.olean.private` size. The CPU time is measured under load, as the build will run: after one run
# alone (for its memory), as many copies as there will be workers run at once (fewer if memory is
# short), and their median CPU time is used. A process sharing the machine runs slower (two
# hyperthreads share a core; clocks drop with every core busy) and its CPU time grows to match, so
# this is what makes `wall = CPU ÷ workers` hold on a busy, hyperthreaded machine. When
# the build will run in stages (see "Staging" below), some of them on more workers than the top's
# count, the lower sample is also run with one copy per core (as many as fit), and the CPU time
# per batch is interpolated between the two loads. Fitting CPU time as a fixed cost per module
# plus b·Σ rows·ν (CPU, not wall: wall time on a busy machine is too noisy), disk as
# rows·(a + b·ν) and per-worker memory as c + d·load_max, it projects CPU, wall time (each stage's
# CPU ÷ its workers, stage by stage), peak memory, worker counts and disk for everything still to
# build, and saves the fit to `.lake/build-estimate-<kernel|native>.json`, which later runs of the
# same kind use in place of the constants below. The sample batches stay built.
#
# The Python parts (the estimate, the disk check, the stage plan) are in `build_tools.py`.
#
# Proof terms. Once a batch is built, `lake build` never reads its proof term again (see
# `proofs.sh`), so with `--proofs=discard` or `--proofs=archive` each batch's `.olean.private` is
# shrunk as soon as Lake finishes it, by `proofs.sh` running alongside the build at low priority.
# Only the batches in flight are ever full-size on disk. `./proofs.sh restore` gives them back.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

SHARED_GB=2.5      # imported oleans, mapped once and shared by every worker
BASE_GB=0.6        # per-worker private memory independent of the batch
PER_ROW_NU_GB=2.4e-5  # per-worker private memory per batch row per unit of ν, proof term included
ROW_KB=48          # proof-term disk per batch row independent of height
ROW_NU_KB=3.24     # proof-term disk per batch row per unit of ν
DISK_WARN=0.5      # warn when the proof terms would take this share of the free disk

PROOFS=keep
NATIVE=0
ESTIMATE=0
RETRIES=3          # the kernel's precisionRetriesRS (Zeta/Zeros/BuildCertsRS.lean), unless --retries
args=()
while (( $# )); do
  case $1 in
    --native) NATIVE=1 ;;
    --estimate) ESTIMATE=1 ;;
    --proofs=keep|--proofs=discard|--proofs=archive) PROOFS=${1#--proofs=} ;;
    --proofs=*) echo "build.sh: --proofs must be keep, discard or archive" >&2; exit 2 ;;
    --retries|--retries=*)
      if [[ $1 == --retries ]]; then RETRIES=${2:-}; shift; else RETRIES=${1#--retries=}; fi
      [[ $RETRIES =~ ^[0-9]+$ ]] || { echo "build.sh: --retries needs a number" >&2; exit 2; }
      # read by the kernel metaprogram (`retriesRS`): a failing row's precision is raised this often
      export ZETA_RS_RETRIES=$RETRIES ;;
    *) args+=("$1") ;;
  esac
  shift
done
set -- ${args[@]+"${args[@]}"}
if (( NATIVE )); then
  if [[ $PROOFS != keep ]]; then
    echo "build.sh: --native builds no kernel-checked Riemann–Siegel batch; drop --proofs" >&2
    exit 2
  fi
  (( $# )) || set -- Native
fi

# the largest batch's rows·ν, from the zero stores' manifests and the generator's batch sizes
load_max=$(python3 build_tools.py load-max 2>/dev/null || echo 12000)

cores=0; avail_gb=0
case "$(uname -s)" in
  Darwin) cores=$(sysctl -n hw.ncpu 2>/dev/null || echo 0)
          total=$(sysctl -n hw.memsize 2>/dev/null || echo 0)
          pct=$(memory_pressure 2>/dev/null | awk -F': ' '/free percentage/ { sub(/%/, "", $2); print $2 }')
          if [[ -n "${pct:-}" && "$total" -gt 0 ]]; then
            avail_gb=$(awk -v t="$total" -v p="$pct" 'BEGIN { printf "%.1f", t * p / 100 / 1073741824 }')
          else
            # `vm_stat` reports pages; its header carries the page size
            avail_gb=$(vm_stat 2>/dev/null | awk '
              /page size of/ { ps = $8 }
              /^Pages (free|inactive|speculative|purgeable):/ { sub(/\./, "", $NF); n += $NF }
              END { printf "%.1f", (ps ? n * ps / 1073741824 : 0) }')
          fi ;;
  Linux)  cores=$(nproc 2>/dev/null || echo 0)
          avail_gb=$(awk '/MemAvailable/ { printf "%.1f", $2 / 1048576 }' /proc/meminfo 2>/dev/null || echo 0)
          # The native checker's plugin chain links `libLake_shared.so`, which the loader does not
          # find for a `dlopen`ed library unless the toolchain's library directory is on the path
          # (macOS finds it through `lean`'s rpath).
          if (( NATIVE )); then
            export LD_LIBRARY_PATH="$(lean --print-libdir)${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
          fi ;;
esac

MODE=kernel; (( NATIVE )) && MODE=native
ESTIMATE_FILE=.lake/build-estimate-$MODE.json

if (( NATIVE )); then
  # the native checker's memory grows slowly with height, so it has its own model constants
  BASE_GB=0.25
  PER_ROW_NU_GB=2.5e-6
fi

# Measured constants from an earlier `--estimate` of the same kind replace the defaults above.
# Not when this build's largest rows·ν is more than twice the sampled one (the fit is linear and
# only measured up to there), nor from an estimate made before the rows·ν model. Otherwise
# `unmeasured` says why, for the banner below.
unmeasured="no --estimate of a $MODE build ($ESTIMATE_FILE)"
if [[ -f $ESTIMATE_FILE ]] && (( ! ESTIMATE )); then
  measured=$(python3 build_tools.py constants "$ESTIMATE_FILE" "$load_max")
  if [[ $measured == stale* ]]; then
    unmeasured=${measured#stale }
  else
    unmeasured=
    read -r SHARED_GB BASE_GB PER_ROW_NU_GB ROW_KB ROW_NU_KB measured_on <<< "$measured"
    echo "build.sh: using the constants measured by --estimate on ${measured_on} ($ESTIMATE_FILE)" >&2
  fi
fi

sized=0
if [[ -z "${LEAN_NUM_THREADS:-}" ]]; then
  if [[ "$cores" == 0 || "$avail_gb" == "0" || "$avail_gb" == "0.0" ]]; then
    # could not size the machine: a conservative default
    export LEAN_NUM_THREADS=4
    echo "build.sh: could not detect cores/available memory -> LEAN_NUM_THREADS=4" \
         "(override by setting LEAN_NUM_THREADS)" >&2
  else
    per_worker=$(awk -v b="$BASE_GB" -v k="$PER_ROW_NU_GB" -v n="$load_max" 'BEGIN { printf "%.2f", b + k * n }')
    by_mem=$(awk -v r="$avail_gb" -v s="$SHARED_GB" -v w="$per_worker" \
               'BEGIN { n = int((r - s) / w); print (n < 1 ? 1 : n) }')
    export LEAN_NUM_THREADS=$(( cores < by_mem ? cores : by_mem ))
    sized=1
    echo "build.sh: ${cores} cores, ${avail_gb} GB available; at the largest batch (rows·ν ${load_max}," \
         "≈ ${per_worker} GB per worker) ${LEAN_NUM_THREADS} workers fit ->" \
         "LEAN_NUM_THREADS=${LEAN_NUM_THREADS} (override by setting LEAN_NUM_THREADS)" >&2
  fi
else
  echo "build.sh: LEAN_NUM_THREADS=${LEAN_NUM_THREADS} (from environment)" >&2
fi

if (( ESTIMATE )); then
  exec python3 build_tools.py estimate --mode "$MODE" --cores "$cores" --avail-gb "$avail_gb" \
    --out "$ESTIMATE_FILE"
fi

# Proof-term disk estimate for the batches not yet built, against the free disk. Skipped when
# every target named is outside `Zeta` (e.g. `./build.sh Enclosure`), which builds no batch.
wants_batches=1
if (( $# )); then
  wants_batches=0
  for t in "$@"; do [[ $t == Zeta || $t == Zeta.* ]] && wants_batches=1; done
fi
if (( wants_batches )); then
  python3 build_tools.py disk --proofs "$PROOFS" --row-kb "$ROW_KB" --row-nu-kb "$ROW_NU_KB" \
    --warn "$DISK_WARN" --workers "$LEAN_NUM_THREADS" >&2 || true
fi

# A worker count sized from the default constants (a fit at lower heights) can be far off at this
# height, so say so where it cannot be missed.
if [[ -n $unmeasured ]] && (( sized && (NATIVE || wants_batches) )); then
  {
    echo
    printf '!%.0s' {1..98}; echo
    echo "!! WORKER COUNT NOT MEASURED AT THIS HEIGHT: $unmeasured."
    echo "!! The default constants give ${LEAN_NUM_THREADS} workers (≈ ${per_worker} GB each at rows·ν ${load_max})."
    echo "!! For a measured count, stop and run first (a few minutes):   ./build.sh --estimate$( (( NATIVE )) && echo ' --native')"
    printf '!%.0s' {1..98}; echo
    echo
  } >&2
fi

# The native build also predicts the kernel-checked one: each native batch reports, as lines
# carrying KERNEL_RISK (`kernelRisks` in `Native/BuildCerts.lean`), every zero the kernel will need
# to raise its working precision for, with how many raises (or that none will do). The build's
# output is copied to a log, and those lines, including the ones Lake replays from modules already
# built, are checked against the kernel's retries (RETRIES, `--retries`): the zeros they do not
# cover go into one banner at the end, and the exit status is then 3.
KERNEL_RISK="KERNEL PRECISION"
if (( NATIVE )); then
  lake build Native.PluginCheck
  log=$(mktemp "${TMPDIR:-/tmp}/native-build.XXXXXX")
  rc=0
  lake build "$@" 2>&1 | tee "$log" || rc=$?
  reported=$(grep -F "$KERNEL_RISK" "$log" | sed "s/.*$KERNEL_RISK: //" | sort -u || true)
  rm -f "$log"
  # the reported zeros the kernel's retries do not cover: more raises needed, or none will do
  fails=$(awk -v r="$RETRIES" '
    match($0, /needs [0-9]+ raise/) { k = substr($0, RSTART + 6, RLENGTH - 12) + 0; if (k > r) print; next }
    NF { print }' <<< "$reported")
  covered=$(( $(grep -c . <<< "$reported" || true) - $(grep -c . <<< "$fails" || true) ))
  if (( covered > 0 )); then
    echo "build.sh: $covered zero(s) will need a raised working precision in the kernel build;" \
         "its $RETRIES retries cover them" >&2
  fi
  if [[ -n $fails ]]; then
    k=$(grep -oE 'needs [0-9]+ raise' <<< "$fails" | awk '{ if ($2 > m) m = $2 } END { print m }')
    {
      echo
      printf '!%.0s' {1..98}; echo
      echo "!! THE KERNEL-CHECKED BUILD (./build.sh) WILL FAIL ON THESE ZEROS with $RETRIES retries"
      echo "!! (the native theorem is unaffected; this predicts the kernel run, before it starts):"
      while IFS= read -r line; do echo "!!   $line"; done <<< "$fails"
      if [[ -n $k ]]; then
        echo "!! FIX: run the kernel build with enough retries:   ./build.sh --retries $k"
      fi
      if grep -q "move this endpoint" <<< "$fails"; then
        echo "!! FIX: no retries rescue the zeros marked \"move this endpoint\": regenerate those store rows."
      fi
      printf '!%.0s' {1..98}; echo
    } >&2
    (( rc )) || rc=3
  fi
  exit $rc
fi

# Staging. The worker count above is sized for the largest batch, but lower batches (200 rows, small
# ν) need less memory each, so more workers fit lower down. When batches still to build fit more workers than that, the
# build runs in stages up the height, each building a run of consecutive group modules (and so
# their batches) on as many workers as fit at its highest batch, then a last stage building the
# rest on the count sized for the top; `plan_stages` in `build_tools.py` places the boundaries.
# Only for a default build (no targets named) whose worker count was sized here, not set in the
# environment.
stages=()
if (( sized && $# == 0 && cores > LEAN_NUM_THREADS )); then
  plan=$(python3 build_tools.py stages --cores "$cores" --avail-gb "$avail_gb" \
         --shared-gb "$SHARED_GB" --base-gb "$BASE_GB" --per-row-nu-gb "$PER_ROW_NU_GB" \
         --last "$LEAN_NUM_THREADS" || true)
  if [[ -n $plan ]]; then
    while IFS= read -r line; do stages+=("$line"); done <<< "$plan"
    echo "build.sh: ${#stages[@]} stages up the height, then the rest on ${LEAN_NUM_THREADS} workers:" >&2
    for line in "${stages[@]}"; do
      read -r w top todo groups <<< "$line"
      read -r -a groups <<< "$groups"
      echo "build.sh:   ${w} workers: ${#groups[@]} groups up to t ≈ ${top} (${todo} batches to build)" >&2
    done
  fi
fi

# --proofs=discard|archive: `proofs.sh` shrinks each batch as Lake finishes it. Lake writes a
# module's `.trace` last, so a `.trace` newer than a marker means Lake is done with that batch's
# files. Each pass looks only at batches finished since the previous pass (a moving marker, touched
# before the scan, so a batch finishing mid-scan is seen again next time); the final pass sweeps
# everything since the start, so a failed or missed shrink is retried once. Shrinks run under
# `nice`, single-threaded, so they take only the cycles the Lean workers leave, and quietly: their
# per-batch lines would interleave with Lake's progress line (errors still print; `./proofs.sh
# status` counts them afterwards).
LIB=.lake/build/lib/lean/Zeta/Zeros/Certificates
shrink_ready() {  # shrink_ready <marker>
  find "$LIB" -name 'Batch*.trace' -newer "$1" 2>/dev/null | sed -E "s|^$LIB/||; s|\.trace$||" |
    xargs -P "$LEAN_NUM_THREADS" -I{} nice -n 19 ./proofs.sh "$PROOFS" {} >/dev/null
}

# run_lake <workers> [targets…]: one `lake build` on that many workers, shrinking proof terms as
# it goes unless --proofs=keep
run_lake() {
  local workers=$1; shift
  if [[ $PROOFS == keep ]]; then
    LEAN_NUM_THREADS=$workers lake build "$@"
    return
  fi
  local start next prev pid rc=0 failed=0
  start=$(mktemp "${TMPDIR:-/tmp}/build.XXXXXX")
  LEAN_NUM_THREADS=$workers lake build "$@" &
  pid=$!
  prev=$start
  while kill -0 "$pid" 2>/dev/null; do
    next=$(mktemp "${TMPDIR:-/tmp}/build.XXXXXX")
    shrink_ready "$prev" || failed=1
    [[ $prev == "$start" ]] || rm -f "$prev"
    prev=$next
    sleep 5
  done
  wait "$pid" || rc=$?
  [[ $prev == "$start" ]] || rm -f "$prev"
  shrink_ready "$start" || failed=1
  rm -f "$start"
  (( failed == 0 )) || echo "build.sh: some proof terms were not shrunk (see above); \`./proofs.sh status\`" >&2
  return $rc
}

[[ $PROOFS == keep ]] || echo "build.sh: --proofs=$PROOFS: each batch's proof term is shrunk as it finishes" >&2
rc=0
for line in ${stages[@]+"${stages[@]}"}; do
  read -r w top todo groups <<< "$line"
  read -r -a groups <<< "$groups"
  echo "build.sh: stage: ${#groups[@]} groups up to t ≈ ${top} on ${w} workers" >&2
  # a failed batch does not stop the later stages (as within one `lake build`, the rest still gets
  # built)
  run_lake "$w" "${groups[@]}" || rc=$?
done
(( ${#stages[@]} == 0 )) || echo "build.sh: last stage: the rest on ${LEAN_NUM_THREADS} workers" >&2
run_lake "$LEAN_NUM_THREADS" "$@" || rc=$?
exit $rc
