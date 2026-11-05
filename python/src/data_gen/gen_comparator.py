#!/usr/bin/env python3
"""Generate the comparator targets that let the certificate batches be verified separately.

The proof of `Zeta.riemannHypothesisUpTo_<T>` factors through the batches' exported
statements: each batch module proves one `BatchSpec n an ad bn bd`, and nothing downstream reads a
batch's proof. So besides the global `comparator/Main` check this writes, under `comparator/`:

    Batches/Statements.lean
        # one name per batch for its exported statement, `Comparator.Spec.RS0001 : Prop :=
        #   BatchSpec …`, shared by the batch targets and the reduction
    Batches/<Method>/BatchNNNN/{Challenge,Solution}.lean, config.json
        # one target per batch: the challenge states `Spec.<batch>` (proved by `sorry`), the
        #   solution cites the batch's theorem
    Reduction/{Challenge,Solution}.lean, config.json
        # every batch's `BatchSpec`, as hypotheses, implies RH up to T; the solution folds them
        #   with `BatchSpec.append` exactly as the assembler does and imports no batch

If every batch target and the reduction pass, the main theorem follows: the reduction assumes
exactly the named statements `Spec.<batch>` that the batch targets prove, and comparator checks that
every target sees the same definition of each name. (`Statements.lean` is written from the same
batch plan as `gen_zero_certificates.py`, which is what makes the batches' own statements.)
`comparator/shard.sh` runs any set of batch targets as one comparator run, so the fixed cost of a
run is paid per shard.

Run from the project root, after `gen_zero_certificates.py` on the same stores:
    PYTHONPATH=python/src python3 python/src/data_gen/gen_comparator.py comparator [<store>…]
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from data_gen.gen_zero_certificates import (BatchRef, default_stores, gram_cap, header,
                                             plan_batches, write_module)

#: the axioms every target may use
PERMITTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]

#: `RiemannHypothesisUpTo T` written out, so a challenge needs only Mathlib's `riemannZeta`
RH_UP_TO = ("∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < {T} →\n"
            "      s.re = 1 / 2")


def spec(ref: BatchRef) -> str:
    """The shared name of a batch's exported statement, in namespace `Comparator`."""
    return f"Spec.{ref.seam_tag}"


def statements_file(refs: list[BatchRef], src: str) -> str:
    note = ("One name per certificate batch for its exported statement, shared by the batch\n"
            "targets (which prove it) and the reduction (which assumes it).")
    def one(r: BatchRef) -> str:
        line = f"abbrev {spec(r)} : Prop := Zeta.Certificates.{r.spec}"
        if len(line) > 100:  # high batches with long endpoint literals
            line = f"abbrev {spec(r)} : Prop :=\n  Zeta.Certificates.{r.spec}"
        return f"/-- The statement exported by batch {r.qual}. -/\n{line}"
    defs = "\n\n".join(one(r) for r in refs)
    return header(src, note) + f"""import Zeta.Zeros.Certificates.Basic

namespace Comparator

{defs}

end Comparator
"""


def target(ref: BatchRef) -> str:
    """The comparator theorem name for a batch, unique across methods."""
    return f"batch_{ref.seam_tag}"


def config(module: str, names: list[str]) -> str:
    return json.dumps({
        "challenge_module": f"{module}.Challenge",
        "solution_module": f"{module}.Solution",
        "theorem_names": [f"Comparator.{n}" for n in names],
        "permitted_axioms": PERMITTED_AXIOMS,
        "enable_nanoda": False,
    }, indent=4) + "\n"


def batch_files(ref: BatchRef, src: str) -> dict[str, str]:
    stmt = spec(ref)
    note_c = f"Comparator challenge for batch {ref.qual}: its exported statement, by `sorry`."
    note_s = f"Comparator solution for batch {ref.qual}: the batch's own theorem."
    challenge = header(src, note_c) + f"""import Batches.Statements

namespace Comparator

theorem {target(ref)} : {stmt} :=
  sorry

end Comparator
"""
    solution = header(src, note_s) + f"""import Batches.Statements
import Zeta.Zeros.Certificates.{ref.qual}

namespace Comparator

theorem {target(ref)} : {stmt} :=
  Zeta.Certificates.{ref.qual}.batch

end Comparator
"""
    module = f"Batches.{ref.qual}"
    return {"Challenge.lean": challenge, "Solution.lean": solution,
            "config.json": config(module, [target(ref)])}


def reduction_files(refs: list[BatchRef], height: int, src: str) -> dict[str, str]:
    hyps = "\n".join(f"    (h_{r.seam_tag} : {spec(r)})" for r in refs)
    concl = RH_UP_TO.format(T=height)
    note_c = ("Comparator challenge for the reduction: every certificate batch's exported\n"
              f"statement, as a hypothesis, implies the Riemann hypothesis up to height {height}.\n"
              "Proved by `sorry`.")
    note_s = ("Comparator solution for the reduction: the batch statements are folded with\n"
              "`BatchSpec.append` exactly as the assembler `Zeta.Zeros.Certificates` does, and\n"
              "the total fed to `riemannHypothesisUpTo_of_batchSpec`. No batch module is imported.")
    challenge = header(src, note_c) + f"""import Mathlib.NumberTheory.LSeries.RiemannZeta
import Batches.Statements

namespace Comparator

theorem riemannHypothesisUpTo_of_batches
{hyps} :
    {concl} :=
  sorry

end Comparator
"""
    first = refs[0]
    a0, ad0 = first.first
    steps = [f"  have u_{first.seam_tag} := h_{first.seam_tag}"]
    total = first.count
    for prev, cur in zip(refs, refs[1:]):
        total += cur.count
        bn, bd = cur.last
        steps.append(f"  have u_{cur.seam_tag} : BatchSpec {total} {a0} {ad0} {bn} {bd} :=\n"
                     f"    BatchSpec.append u_{prev.seam_tag} h_{cur.seam_tag} rfl rfl rfl")
    last = refs[-1]
    solution = header(src, note_s) + f"""import Batches.Statements
import Zeta.Zeros.Certificates.Fold
import Zeta.Zeros.RiemannHypothesisUpTo.Basic
import Zeta.Gram.Certificates

open Zeta.Certificates Zeta.Certificates.Gram

namespace Comparator

theorem riemannHypothesisUpTo_of_batches
{hyps} :
    {concl} := by
{chr(10).join(steps)}
  intro s h_zero h_nontrivial h_one h_im
  refine riemannHypothesisUpTo_of_batchSpec certifiedGramBlockSeq u_{last.seam_tag} (by decide) ?_
    s h_zero h_nontrivial h_one
    (h_im.trans_le ((show ({height} : ℝ) ≤ gp1.fst by norm_num).trans
      (GramPoint.certificate_left_lt_gramPoint gp1_cert).le))
  refine le_trans ?_ certifiedGramBlockSeq.head_left_le_gramPoint
  norm_num [certifiedGramBlockSeq, Enclosure.sfrac]

end Comparator
"""
    return {"Challenge.lean": challenge, "Solution.lean": solution,
            "config.json": config("Reduction", ["riemannHypothesisUpTo_of_batches"])}


def headline_height(root: Path) -> int:
    """`T` of the headline `riemannHypothesisUpTo_<T>` in `Zeta/Main.lean`: the reduction proves the
    same statement."""
    m = re.search(r"theorem riemannHypothesisUpTo_(\d+)\b", (root / "Zeta/Main.lean").read_text())
    if not m:
        raise SystemExit("no `theorem riemannHypothesisUpTo_<T>` in Zeta/Main.lean")
    return int(m.group(1))


def main() -> None:
    if len(sys.argv) < 2:
        raise SystemExit("usage: gen_comparator.py <comparator_dir> [<store>…]")
    out = Path(sys.argv[1])
    stores = [Path(a) for a in sys.argv[2:]] or default_stores()
    plan = plan_batches(stores, gram_cap())
    refs = [p[0] for p in plan]
    srcs = ", ".join(dict.fromkeys(str(p[3]) for p in plan))
    height = headline_height(out.resolve().parent)

    (out / "Batches").mkdir(parents=True, exist_ok=True)
    write_module(out / "Batches" / "Statements.lean", statements_file(refs, srcs))
    for ref in refs:
        d = out.joinpath("Batches", *ref.qual.split("."))
        d.mkdir(parents=True, exist_ok=True)
        for name, text in batch_files(ref, srcs).items():
            write_module(d / name, text)
    d = out / "Reduction"
    d.mkdir(parents=True, exist_ok=True)
    for name, text in reduction_files(refs, height, srcs).items():
        write_module(d / name, text)
    print(f"wrote {len(refs)} batch targets + the reduction (height {height}) under {out}")


if __name__ == "__main__":
    main()
