#!/usr/bin/env bash
# Run comparator on one target's config, e.g.
#   comparator/run.sh comparator/Reduction/config.json
#
# The tools are per-machine, in `.comparator-tools/bin/`: `comparator` and `lean4export` (see
# leanprover/comparator). `landrun`, the sandbox around a possibly hostile solution, is used if it
# is on the PATH (Linux only); otherwise `fake-landrun.sh` runs the export unsandboxed.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
T=$PWD/.comparator-tools/bin
for f in comparator lean4export; do
  [[ -x $T/$f ]] ||
    { echo "run.sh: $T/$f missing: install it from leanprover/comparator" >&2; exit 2; }
done
LANDRUN=$(command -v landrun || echo "$T/fake-landrun.sh")
COMPARATOR_LANDRUN=$LANDRUN COMPARATOR_LEAN4EXPORT=$T/lean4export \
  lake env "$T/comparator" "$1"
