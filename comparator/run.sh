#!/usr/bin/env bash
# Run comparator on one target's config; with no argument, the global check of the main theorem.
#   comparator/run.sh --force
#   comparator/run.sh comparator/Reduction/config.json
# The global check needs `--force`: exporting everything at once is very slow beyond height 1e4,
# so `comparator/sharded_run.sh` is the usual route.
#
# The tools are per-machine: a checkout of leanprover/comparator, built in `.comparator-tools/` (see
# the Comparator section of README.md). `landrun`, the sandbox around a possibly hostile solution,
# is used if it is on the PATH (Linux only); otherwise `fake-landrun.sh` runs the export unsandboxed.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
T=$PWD/.comparator-tools
COMPARATOR=$T/.lake/build/bin/comparator
LEAN4EXPORT=$T/.lake/packages/lean4export/.lake/build/bin/lean4export
for f in "$COMPARATOR" "$LEAN4EXPORT"; do
  [[ -x $f ]] || { echo "run.sh: $f missing: see the Comparator section of README.md" >&2; exit 2; }
done
LANDRUN=$(command -v landrun || echo "$T/scripts/fake-landrun.sh")
force=0
if [[ ${1:-} == --force ]]; then force=1; shift; fi
config=${1:-comparator/Main/config.json}
use_sharded="the global check needs every proof at once; use comparator/sharded_run.sh instead"
if [[ $config == */Main/config.json ]] && (( ! force )); then
  echo "run.sh: the global check is slow beyond height 1e4: exporting many large proofs at once can take hours or weeks. Use comparator/sharded_run.sh instead, or pass --force to run it anyway." >&2
  exit 2
fi

log=$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX")
trap 'rm -f "$log"' EXIT
COMPARATOR_LANDRUN=$LANDRUN COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT \
  lake env "$COMPARATOR" "$config" 2>&1 | tee "$log" || {
  rc=$?
  if (( rc == 137 )) || grep -Eqi 'no space left|out of memory|cannot allocate|bad_alloc' "$log"; then
    echo "run.sh: ran out of disk or memory: $use_sharded" >&2
  fi
  if grep -q 'invalid header' "$log"; then
    echo "run.sh: a private olean cannot be read, most likely a placeholder from --proofs=discard" >&2
    echo "run.sh: see scripts/proofs.sh status, and rebuild those batches with scripts/proofs.sh restore" >&2
  fi
  exit "$rc"
}
