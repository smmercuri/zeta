#!/usr/bin/env bash
# Regenerate every certificate module from the stores under `python/out/`, and move the
# hand-written headline files to the height those stores support.
#
#   scripts/gen_certificates.sh          # height ⌊gp1.fst⌋, the largest the gram store supports
#   scripts/gen_certificates.sh --height H     # a smaller headline height
#   scripts/gen_certificates.sh --comparator   # also the per-batch comparator targets + the reduction
#                                        #   (`gen_comparator.py`; one directory per batch)
#   scripts/gen_certificates.sh --ignore-style # allow lines past the generators' 100-column limit, for
#                                        #   stores with long endpoints (`--no-widen`)
#   PYTHON=python3.12 scripts/gen_certificates.sh   # the interpreter (default python3; the generators
#                                        #   are stdlib-only, so no Sage env is needed)
#
# In order:
#   1. the height H: ⌊gp1.fst⌋ of the gram store's first gram point (or --height, which must not
#      exceed it), and the height H₀ the headline files state now;
#   2. if H ≠ H₀, every standalone H₀ in the hand-written headline files becomes H (theorem names,
#      statements, docstrings, the `#guard_msgs` axiom listing):
#        Zeta/Main.lean  Native/Main.lean  comparator/Main/{Challenge,Solution}.lean, config.json
#   3. the generators: kernel batches, groups and assembler (`gen_zero_certificates.py --prune`),
#      gram certificates, count certificate, native shards, groups, assembler and count
#      certificate (`gen_native_certificates.py --prune`), with --comparator `gen_comparator.py --prune`.
# `Zeta.lean` needs no update: it lists none of the generated batch or group modules
# (`mk_all.sh`), so regenerating them never changes it.
#
# `--prune` deletes certificate modules generated earlier that this run does not rewrite (the
# store shrank); only files carrying their generator's `AUTO-GENERATED` header are touched.
# Prose elsewhere that names the height (README, formalization.yaml, the blueprint) is updated by
# hand.
set -euo pipefail
cd "$(dirname "$0")/.."

PYTHON=${PYTHON:-python3}
export PYTHONPATH=python/src${PYTHONPATH:+:$PYTHONPATH}
HEADLINES=(Zeta/Main.lean Native/Main.lean comparator/Main/Challenge.lean
           comparator/Main/Solution.lean comparator/Main/config.json)

height=""
comparator=0
style=()
while (( $# )); do
  case "$1" in
    --height) height=${2:?--height needs a value}; shift ;;
    --height=*) height=${1#--height=} ;;
    --comparator) comparator=1 ;;
    --ignore-style) style=(--ignore-style) ;;
    *) echo "usage: scripts/gen_certificates.sh [--height H] [--comparator] [--ignore-style]" >&2; exit 2 ;;
  esac
  shift
done

# 1. the gram store, the height it supports, and the height the headlines state now
gram_top=$("$PYTHON" -c '
import math
from data_gen.gen_count_certificate import default_gram, gram_head
g = default_gram()
print(g, math.floor(gram_head(g)))')
read -r gram top <<< "$gram_top"
if [[ -z $height ]]; then
  height=$top
elif ! [[ $height =~ ^[0-9]+$ ]] || (( height > top )); then
  echo "gen_certificates.sh: --height $height: the gram store supports at most $top" >&2
  exit 1
fi
old=$(sed -nE 's/^theorem riemannHypothesisUpTo_([0-9]+).*/\1/p' Zeta/Main.lean)
[[ -n $old ]] || { echo "gen_certificates.sh: no headline theorem in Zeta/Main.lean" >&2; exit 1; }
for f in "${HEADLINES[@]}"; do
  grep -Eq "riemannHypothesisUpTo_${old}([^0-9]|\$)" "$f" || {
    echo "gen_certificates.sh: $f does not state height $old as Zeta/Main.lean does; fix it by hand" >&2
    exit 1; }
done

# 2. the headline files
if [[ $old != "$height" ]]; then
  perl -pi -e "s/(?<!\\d)${old}(?!\\d)/${height}/g" "${HEADLINES[@]}"
  echo "height $old -> $height in ${HEADLINES[*]}"
else
  echo "height $height (unchanged)"
fi

# 3. the generators
gen=python/src/data_gen
"$PYTHON" $gen/gen_zero_certificates.py Zeta/Zeros --prune ${style[@]+"${style[@]}"}
"$PYTHON" $gen/gen_gram_certificates.py Zeta/Gram/Certificates.lean "$gram" ${style[@]+"${style[@]}"}
"$PYTHON" $gen/gen_count_certificate.py Zeta/Zeros/CountCertificates.lean --height "$height" \
  ${style[@]+"${style[@]}"}
"$PYTHON" $gen/gen_native_certificates.py Native --prune ${style[@]+"${style[@]}"}
if (( comparator )); then
  "$PYTHON" $gen/gen_comparator.py comparator --prune ${style[@]+"${style[@]}"}
fi
