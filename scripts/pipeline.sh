#!/usr/bin/env bash
# From a height to Lean certificates: search for the zeros and the Gram block, then generate the
# certificates, and optionally build them. Run it in the `zeta` conda environment.
#
#   scripts/pipeline.sh HEIGHT [options]  # e.g. scripts/pipeline.sh 1e4 --build
#
# The search:
#   --workers N            worker processes for both searches (default: every core)
#   --no-widen             store unwidened intervals; also passes --ignore-style to the generators
#   --bisection-depth D    bisections per interval in both searches (default: none)
#   --em-args "…"          more options for `store_zeros.py euler_maclaurin`, e.g. "--M 30 --b 1.5"
#   --rs-args "…"          more options for `store.py riemann_siegel`, e.g. "--window-retries 200"
#
# The certificates:
#   --no-comparator        do not regenerate the comparator targets. They are also skipped, with a
#                          message, above 10,000 batches (each batch writes its own directory)
#   --force                overwrite uncommitted changes to generated files
#
# The build (off by default):
#   --build                `scripts/build.sh --estimate`, which builds the libraries first, then `scripts/build.sh`
#                          with --proofs=auto: proof terms are kept, archived or discarded to fit
#                          the disk, and it stops if even discarding would not leave room
#   --time                 with --build: delete the certificates' build outputs after the estimate
#                          and time building them all, with the libraries already built
#   --native               with --build: build the `Native` library instead
#   --endpoint             with --native: native as the result, without predicting the kernel
#                          build (`build.sh --native --endpoint`); use it to time the native layer
#   --build-args "…"       more options for the final `scripts/build.sh`; "--proofs=keep" overrides the
#                          automatic choice
#
# Runs in order, stopping at the first failure:
#   1. `store_zeros.py euler_maclaurin 1 149.5 --M 20`
#   2. `store.py riemann_siegel 149.5 HEIGHT`
#   3. `gen_certificates.sh`, then `gen_comparator.py`
# The theorem's final height is the Gram point the search finds at or above HEIGHT.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' scripts/pipeline.sh >&2; exit 2; }
note() { echo "pipeline.sh: $*" >&2; }
die() { note "$*"; exit 1; }
# `set -e` exits without a message; say where.
trap 'note "failed at line $LINENO (exit $?)"' ERR
dur() {
  local s=$1
  if (( s >= 3600 )); then printf '%dh%02dm' $(( s / 3600 )) $(( s % 3600 / 60 ))
  elif (( s >= 60 )); then printf '%dm%02ds' $(( s / 60 )) $(( s % 60 ))
  else printf '%ds' "$s"
  fi
}

PYTHON=${PYTHON:-python}
export PYTHONPATH=python/src${PYTHONPATH:+:$PYTHONPATH}
SPLIT=149.5
COMPARATOR_MAX_BATCHES=10000
GENERATED=(python/out Zeta/Zeros Zeta/Gram Zeta/Main.lean Native comparator/Batches comparator/Main
           comparator/Reduction)

height="" comparator=1 force=0 build=0 timed=0 native=0 endpoint=0
search=() em=() rs=() gen=() style=() final=()
while (( $# )); do
  case "$1" in
    --workers) search+=(--num-workers "${2:?--workers needs a value}"); shift ;;
    --no-widen) search+=(--no-widen); gen+=(--ignore-style); style=(--ignore-style) ;;
    --bisection-depth) search+=(--bisection-depth "${2:?--bisection-depth needs a value}"); shift ;;
    --em-args) read -r -a em <<< "${2?--em-args needs a value}"; shift ;;
    --rs-args) read -r -a rs <<< "${2?--rs-args needs a value}"; shift ;;
    --no-comparator) comparator=0 ;;
    --force) force=1 ;;
    --build) build=1 ;;
    --time) timed=1 ;;
    --native) native=1 ;;
    --endpoint) endpoint=1 ;;
    --build-args) read -r -a final <<< "${2?--build-args needs a value}"; shift ;;
    -h|--help) usage ;;
    -*) note "unknown option $1"; usage ;;
    *) [[ -z $height ]] || usage; height=$1 ;;
  esac
  shift
done
[[ -n $height ]] || usage
(( ! timed || build )) || die "--time needs --build"
(( ! native || build )) || die "--native needs --build"
(( ! endpoint || native )) || die "--endpoint needs --native"
python3 -c 'import sys; sys.exit(0 if float(sys.argv[1]) > float(sys.argv[2]) else 1)' "$height" "$SPLIT" \
  2> /dev/null || die "HEIGHT must be a number above $SPLIT, got '$height'"

# The stores are written under `PROJECT_ROOT` in config.py: this checkout.
root=$("$PYTHON" -c 'import os; from config import PROJECT_ROOT
print(os.path.realpath(os.path.expanduser(PROJECT_ROOT)))') ||
  die "could not read PROJECT_ROOT with '$PYTHON' (activate the zeta environment?)"
[[ $root == "$(pwd -P)" ]] ||
  die "config.py writes the stores to $root, not this checkout ($(pwd -P)); set PROJECT_ROOT first"
"$PYTHON" -c 'import sage.all' 2> /dev/null ||
  die "'$PYTHON' cannot import Sage; run 'conda activate zeta' first (see python/README.md)"
if (( ! force )); then
  dirty=$(git status --porcelain -- "${GENERATED[@]}" | wc -l | tr -d ' ')
  (( dirty == 0 )) ||
    die "$dirty uncommitted generated files would be overwritten; commit them or pass --force"
fi

note "branch $(git branch --show-current), height $height"
started=$SECONDS

note "1/3: Euler-Maclaurin zeros, 1 to $SPLIT"
"$PYTHON" python/src/data_gen/store_zeros.py euler_maclaurin 1 "$SPLIT" --M 20 \
  ${search[@]+"${search[@]}"} ${em[@]+"${em[@]}"}

note "2/3: Riemann-Siegel zeros and Gram block, $SPLIT to $height"
"$PYTHON" python/src/data_gen/store.py riemann_siegel "$SPLIT" "$height" \
  ${search[@]+"${search[@]}"} ${rs[@]+"${rs[@]}"}

note "3/3: Lean certificates"
scripts/gen_certificates.sh ${gen[@]+"${gen[@]}"}
if (( comparator )); then
  batches=$(find Zeta/Zeros/Certificates -name 'Batch*.lean' | wc -l | tr -d ' ')
  if (( batches > COMPARATOR_MAX_BATCHES )); then
    note "over $COMPARATOR_MAX_BATCHES batches: comparator targets NOT regenerated, so they are now stale"
  else
    "$PYTHON" python/src/data_gen/gen_comparator.py comparator --prune ${style[@]+"${style[@]}"}
  fi
else
  note "--no-comparator: comparator targets NOT regenerated, so they are now stale"
fi

final_height=$(sed -nE 's/^theorem riemannHypothesisUpTo_([0-9]+).*/\1/p' Zeta/Main.lean)
note "certificates generated up to height $final_height in $(dur $(( SECONDS - started )))"
(( build )) || exit 0

mode=() certs=Zeta/Zeros/Certificates
if (( native )); then mode=(--native); certs=Native/Certificates; fi
if (( endpoint )); then mode+=(--endpoint); fi
if (( ! native )) && [[ " ${final[*]-} " != *" --proofs="* ]]; then final+=(--proofs=auto); fi

note "build: estimating, which also builds the libraries"
log=$(mktemp "${TMPDIR:-/tmp}/pipeline.XXXXXX")
trap 'rm -f "$log"' EXIT
if ! scripts/build.sh --estimate ${mode[@]+"${mode[@]}"} 2>&1 | tee "$log"; then
  grep -q 'nothing to estimate' "$log" || die "build.sh --estimate failed"
  note "build: nothing to estimate, every certificate is already built"
fi

if (( timed )); then
  # Otherwise the estimate's sample batches, and anything built earlier, would not be timed.
  rm -rf ".lake/build/lib/lean/$certs" ".lake/build/ir/$certs"
  note "build: timing a build of all certificates, with the libraries already built"
  TIMEFORMAT='pipeline.sh: build took %R s wall, %U s user, %S s system'
  time scripts/build.sh ${mode[@]+"${mode[@]}"} ${final[@]+"${final[@]}"}
else
  note "build: building"
  scripts/build.sh ${mode[@]+"${mode[@]}"} ${final[@]+"${final[@]}"}
fi
note "done: height $final_height, $(dur $(( SECONDS - started ))) in total"
