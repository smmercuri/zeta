#!/usr/bin/env bash
# Verify the certificate batches with comparator, in shards, so only a few batches' proofs are on
# disk at once. With no options: the reduction and every batch, which together establish the
# statement of the main theorem. With --sample: a reproducible random selection, and no reduction.
#
#   comparator/sharded_run.sh [--size 10] [--jobs 1]
#   comparator/sharded_run.sh --sample 300 --seed <public value, e.g. the release commit> [--size 10] [--jobs 1]
#
# --jobs N checks N shards at once, starting a new one whenever one finishes, and each needs memory
# for its own export. Lake runs one build at a time per checkout, so a single builder prepares the
# next few shards while the others are being checked. A batch that is a placeholder (`--proofs=discard`) is restored
# first. Batches this script had to build are discarded again once their shard passes; proofs that
# were already there are kept. Progress is recorded per commit and set of batch statements, so an
# interrupted run resumes where it stopped; Ctrl-C also stops any shards running in the background.
# Each stage and its timing are printed, and the full output goes to logs under
# `comparator/Shard/`. Needs the batch targets (`scripts/gen_certificates.sh --comparator`).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

usage() { awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0" >&2; exit 2; }
note() { echo "sharded_run.sh: $*" >&2; }
dur() {
  local s=$1
  if (( s >= 3600 )); then printf '%dh%02dm' $(( s / 3600 )) $(( s % 3600 / 60 ))
  elif (( s >= 60 )); then printf '%dm%02ds' $(( s / 60 )) $(( s % 60 ))
  else printf '%ds' "$s"
  fi
}

# Each background job runs under a small supervisor, as the leader of its own process group, so that
# `stop` can reach all of its children. The supervisor also stops the group if this script dies
# without running `stop`, as when it is killed outright.
# shellcheck disable=SC2016  # Python, not shell
supervise='
import os, signal, sys, time
parent = os.getppid()
os.setpgid(0, 0)
child = os.fork()
if child == 0:
    os.execvp(sys.argv[1], sys.argv[1:])
while True:
    pid, status = os.waitpid(child, os.WNOHANG)
    if pid:
        sys.exit(os.WEXITSTATUS(status) if os.WIFEXITED(status) else 128 + os.WTERMSIG(status))
    if os.getppid() != parent:
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        os.killpg(0, signal.SIGTERM)
        time.sleep(5)
        os.killpg(0, signal.SIGKILL)
    time.sleep(1)
'
own_group=(python3 -c "$supervise")
running=()
builder=""
stop() {
  trap '' INT TERM HUP
  local -a groups=()
  local p i alive
  for p in "$builder" ${running[@]+"${running[@]}"}; do
    if [[ -n $p ]]; then groups+=("$p"); fi
  done
  for p in ${groups[@]+"${groups[@]}"}; do kill -TERM -- "-$p" 2> /dev/null || true; done
  for (( i = 0; i < 10; i++ )); do
    alive=0
    for p in ${groups[@]+"${groups[@]}"}; do
      if kill -0 -- "-$p" 2> /dev/null; then alive=1; fi
    done
    if (( ! alive )); then break; fi
    sleep 0.5
  done
  for p in ${groups[@]+"${groups[@]}"}; do kill -KILL -- "-$p" 2> /dev/null || true; done
  note "cancelled: shards that finished stay recorded, so running this again resumes"
  exit 130
}
trap stop INT TERM HUP

size=10 jobs=1 sample="" seed=""
while (( $# )); do
  case "$1" in
    --size) size=${2:-}; shift 2 || usage ;;
    --jobs) jobs=${2:-}; shift 2 || usage ;;
    --sample) sample=${2:-}; shift 2 || usage ;;
    --seed) seed=${2:-}; shift 2 || usage ;;
    *) usage ;;
  esac
done
[[ $size =~ ^[1-9][0-9]*$ && $jobs =~ ^[1-9][0-9]*$ ]] || usage
[[ -z $sample || ( $sample =~ ^[1-9][0-9]*$ && -n $seed ) ]] || usage
[[ -f comparator/Batches/Statements.lean ]] ||
  { note "no batch targets: run scripts/gen_certificates.sh --comparator"; exit 2; }

batches=$(find comparator/Batches -name config.json |
  sed -E 's#^comparator/Batches/##; s#/config\.json$##' | LC_ALL=C sort)
if [[ -n $sample ]]; then
  batches=$(python3 -c '
import hashlib, sys
seed, n = sys.argv[1], int(sys.argv[2])
names = sys.stdin.read().split()
key = lambda b: hashlib.sha256(f"{seed}:{b}".encode()).digest()
print("\n".join(sorted(sorted(names, key=key)[:n])))' "$seed" "$sample" <<< "$batches")
fi

run=$(git rev-parse --short=12 HEAD)-$(git hash-object comparator/Batches/Statements.lean | cut -c1-12)
logs=comparator/Shard/logs-$run
mkdir -p "$logs"
passed=comparator/Shard/passed-$run.txt
failed=comparator/Shard/failed-$run.txt
touch "$passed"
: > "$failed"

# Whether the batch's proof term is on disk in full (a placeholder is a few bytes; see `proofs.sh`).
has_proof() {
  local f=.lake/build/lib/lean/Zeta/Zeros/Certificates/$1.olean.private
  [[ -f $f ]] && (( $(wc -c < "$f") > 512 ))
}

reduction=skipped
if [[ -z $sample ]]; then
  if grep -Fxq Reduction "$passed"; then
    reduction=passed
  else
    note "reduction: checking (log: $logs/reduction.log)"
    start=$SECONDS
    "${own_group[@]}" comparator/run.sh comparator/Reduction/config.json \
      < /dev/null > "$logs/reduction.log" 2>&1 &
    builder=$!
    status=0
    wait "$builder" || status=$?
    builder=""
    if (( status == 0 )); then
      echo Reduction >> "$passed"
      reduction=passed
      note "reduction: passed in $(dur $(( SECONDS - start )))"
    else
      reduction=FAILED
      note "reduction: FAILED after $(dur $(( SECONDS - start ))) (see $logs/reduction.log)"
    fi
  fi
fi

# Read into an array first, so that nothing a shard runs can consume the list.
todo=()
while IFS= read -r b; do
  if [[ -n $b ]] && ! grep -Fxq "$b" "$passed"; then todo+=("$b"); fi
done <<< "$batches"
total=$(grep -c . <<< "$batches" || true)
shards=()
for (( i = 0; i < ${#todo[@]}; i += size )); do shards+=("${todo[*]:i:size}"); done
count=${#shards[@]}
note "$total batches selected, ${#todo[@]} to check, in $count shards of up to $size, $jobs at a time"

# Build the given batches, and the small comparator modules of each, so that a shard's own builds
# (which queue on Lake's lock) have almost nothing left to do.
# shellcheck disable=SC2016  # expanded by the inner shell
build_script='
log=$1; shift
rc=0
scripts/proofs.sh restore "$@" >> "$log" 2>&1 || rc=1
mods=()
for b in "$@"; do
  m=${b//\//.}
  mods+=("Zeta.Zeros.Certificates.$m" "Batches.$m.Challenge" "Batches.$m.Solution")
done
lake build "${mods[@]}" >> "$log" 2>&1 || rc=1
exit $rc'

next=0 finished=0 shards_done=0 check_start=$SECONDS
ready=() fresh=() slot_shard=() slot_start=()
build_from=0 build_start=0
for (( j = 0; j < jobs; j++ )); do running[j]=""; done

# Build the next shards in the background, enough to refill the slots.
start_build() {
  local n=$(( jobs - ${#ready[@]} )) b
  local -a names=()
  build_from=$next
  while (( n > 0 && next < count )); do
    fresh[next]=""
    for b in ${shards[next]}; do
      names+=("$b")
      has_proof "$b" || fresh[next]+="$b "
    done
    next=$(( next + 1 ))
    n=$(( n - 1 ))
  done
  build_start=$SECONDS
  note "shards $(( build_from + 1 ))-$next of $count: building ${#names[@]} batches (log: $logs/build.log)"
  "${own_group[@]}" bash -c "$build_script" build "$logs/build.log" "${names[@]}" < /dev/null > /dev/null 2>&1 &
  builder=$!
}

reap_builder() {
  local status=0 s
  if [[ -z $builder ]] || kill -0 "$builder" 2> /dev/null; then return 0; fi
  wait "$builder" || status=$?
  builder=""
  for (( s = build_from; s < next; s++ )); do ready+=("$s"); done
  note "shards $(( build_from + 1 ))-$next: built in $(dur $(( SECONDS - build_start )))"
  if (( status != 0 )); then note "warning: this build reported a problem (see $logs/build.log)"; fi
}

reap_checks() {
  local j s status result
  local -a items
  for (( j = 0; j < jobs; j++ )); do
    if [[ -z ${running[j]} ]] || kill -0 "${running[j]}" 2> /dev/null; then continue; fi
    status=0
    wait "${running[j]}" || status=$?
    running[j]=""
    s=${slot_shard[j]}
    # shellcheck disable=SC2206
    items=(${shards[s]})
    finished=$(( finished + ${#items[@]} ))
    shards_done=$(( shards_done + 1 ))
    if (( status == 0 )); then
      tr ' ' '\n' <<< "${shards[s]}" >> "$passed"
      # shellcheck disable=SC2086
      if [[ -n ${fresh[s]} ]]; then scripts/proofs.sh discard ${fresh[s]} < /dev/null > /dev/null; fi
      result="passed in $(dur $(( SECONDS - slot_start[j] )))"
    else
      tr ' ' '\n' <<< "${shards[s]}" >> "$failed"
      result="FAILED after $(dur $(( SECONDS - slot_start[j] ))) (see $logs/shard-$(( s + 1 )).log)"
    fi
    note "shard $(( s + 1 )) of $count: $result; $finished of ${#todo[@]} batches done," \
      "$(dur $(( SECONDS - check_start ))) so far"
  done
}

start_ready() {
  local j s
  for (( j = 0; j < jobs && ${#ready[@]} > 0; j++ )); do
    if [[ -n ${running[j]} ]]; then continue; fi
    s=${ready[0]}
    ready=("${ready[@]:1}")
    slot_shard[j]=$s
    slot_start[j]=$SECONDS
    note "shard $(( s + 1 )) of $count: exporting and checking"
    # shellcheck disable=SC2086  # the list is meant to split into batch names
    "${own_group[@]}" comparator/shard.sh --name "J$j" ${shards[s]} \
      < /dev/null > "$logs/shard-$(( s + 1 )).log" 2>&1 &
    running[j]=$!
  done
}

while (( shards_done < count )); do
  reap_builder
  reap_checks
  start_ready
  if [[ -z $builder ]] && (( next < count && ${#ready[@]} * 2 <= jobs )); then start_build; fi
  if (( shards_done < count )); then sleep 1; fi
done

ok=$(grep -Fxc -f <(printf '%s\n' "$batches") "$passed" || true)
bad=$(grep -c . "$failed" || true)
if (( ok == total )) && [[ $reduction != FAILED ]]; then
  if [[ -n $sample ]]; then
    note "PASSED: all $total sampled batches passed. A sample does not cover the whole theorem."
  else
    note "VERIFIED: the reduction and all $total batches passed comparator. Together they establish the statement of the main theorem."
  fi
  exit 0
fi
note "INCOMPLETE: $ok of $total batches passed, $bad failed; reduction: $reduction."
if (( bad )); then note "Failed batches are listed in $failed, and their files were kept."; fi
exit 1
