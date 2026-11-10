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
        [--ignore-style]   # allow lines past the 100-column limit (long `--no-widen` endpoints)
        [--prune]          # remove batch targets from an earlier, larger run (else: list, stop)
        [--shards]         # batch targets only, each stating its BatchSpec inline: no shared
                           #   statements and no reduction, for sampled checks at any height
"""
from __future__ import annotations

import inspect
import json
import re
import shutil
import sys
from pathlib import Path

from data_gen.gen_zero_certificates import (BatchRef, default_stores, generated_by, header,
                                             plan_batches, write_module)

#: this generator, as named in the header of every file it writes
SCRIPT = "gen_comparator.py"

# Older releases' planners (v1-1e7, v1-1e8) have `write_module(path, text)` without the style
# argument; accepting both lets this generator write their batch targets too (`--shards`).
_WRITE_TAKES_STYLE = len(inspect.signature(write_module).parameters) >= 3


def write(path: Path, text: str, style: bool) -> None:
    write_module(path, text, style) if _WRITE_TAKES_STYLE else write_module(path, text)


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
    return header(src, note, SCRIPT) + f"""import Zeta.Zeros.Certificates.Basic

namespace Comparator

{defs}

end Comparator
"""


def shards_marker(src: str) -> str:
    """`Statements.lean` in `--shards` mode: no statements, since every target states its own.
    `comparator/sharded_run.sh` looks for this file and names its runs after its hash."""
    note = ("Batch targets only (`gen_comparator.py --shards`): each states its batch's exported\n"
            "statement inline, so there is nothing to share here and no reduction.")
    return header(src, note, SCRIPT)


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


def inline_statement(ref: BatchRef) -> str:
    """A batch's exported statement written out, for a target that imports no shared statements."""
    return f"Zeta.Certificates.{ref.spec}"


def batch_files(ref: BatchRef, src: str, shards: bool = False) -> dict[str, str]:
    stmt = inline_statement(ref) if shards else spec(ref)
    imp = "Zeta.Zeros.Certificates.Basic" if shards else "Batches.Statements"
    head = f"theorem {target(ref)} : {stmt} :="
    if len(head) > 100:  # high batches with long endpoint literals
        head = f"theorem {target(ref)} :\n    {stmt} :="
    note_c = f"Comparator challenge for batch {ref.qual}: its exported statement, by `sorry`."
    note_s = f"Comparator solution for batch {ref.qual}: the batch's own theorem."
    challenge = header(src, note_c, SCRIPT) + f"""import {imp}

namespace Comparator

{head}
  sorry

end Comparator
"""
    solution = header(src, note_s, SCRIPT) + f"""import {imp}
import Zeta.Zeros.Certificates.{ref.qual}

namespace Comparator

{head}
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
    challenge = header(src, note_c, SCRIPT) + f"""import Mathlib.NumberTheory.LSeries.RiemannZeta
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
    solution = header(src, note_s, SCRIPT) + f"""import Batches.Statements
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


def stale_targets(batches: Path, keep: set[Path]) -> list[Path]:
    """The batch target directories under `batches` that this run does not write: left by an
    earlier run over more batches. Only directories whose `Challenge.lean` names this script or
    `gen_zero_certificates.py` as its generator count."""
    return sorted(d for m in batches.iterdir() if m.is_dir() for d in m.glob("Batch*")
                  if d.is_dir() and d not in keep and (d / "Challenge.lean").is_file()
                  and any(generated_by(d / "Challenge.lean", g)
                          for g in (SCRIPT, "gen_zero_certificates.py")))


def main() -> None:
    argv = sys.argv[1:]
    style = "--ignore-style" in argv
    prune = "--prune" in argv
    shards = "--shards" in argv
    argv = [a for a in argv if a not in ("--ignore-style", "--prune", "--shards")]
    if not argv:
        raise SystemExit("usage: gen_comparator.py <comparator_dir> [--ignore-style] [--prune] "
                         "[--shards] [<store>…]")
    out = Path(argv[0])
    stores = [Path(a) for a in argv[1:]] or default_stores()
    plan = plan_batches(stores)
    refs = [p[0] for p in plan]
    srcs = ", ".join(dict.fromkeys(str(p[3]) for p in plan))
    height = None if shards else headline_height(out.resolve().parent)

    keep = {out.joinpath("Batches", *ref.qual.split(".")) for ref in refs}
    stale = stale_targets(out / "Batches", keep) if (out / "Batches").is_dir() else []
    if stale:
        shown = "".join(f"\n  {d}" for d in stale[:5]) + ("\n  …" if len(stale) > 5 else "")
        if not prune:
            raise SystemExit(f"gen_comparator.py: {len(stale)} batch target(s) from an earlier run "
                             f"would be left stale (nothing written):{shown}\n"
                             "re-run with --prune to delete them")
        for d in stale:
            shutil.rmtree(d)
        print(f"pruned {len(stale)} stale batch target(s):{shown}")

    (out / "Batches").mkdir(parents=True, exist_ok=True)
    write(out / "Batches" / "Statements.lean",
                 shards_marker(srcs) if shards else statements_file(refs, srcs), style)
    for ref in refs:
        d = out.joinpath("Batches", *ref.qual.split("."))
        d.mkdir(parents=True, exist_ok=True)
        for name, text in batch_files(ref, srcs, shards).items():
            write(d / name, text, style)
    if shards:
        if (out / "Reduction").is_dir():
            print(f"note: {out / 'Reduction'} is from an earlier run and does not match these targets")
        print(f"wrote {len(refs)} batch targets (inline statements, no reduction) under {out}")
        return
    d = out / "Reduction"
    d.mkdir(parents=True, exist_ok=True)
    for name, text in reduction_files(refs, height, srcs).items():
        write(d / name, text, style)
    print(f"wrote {len(refs)} batch targets + the reduction (height {height}) under {out}")


if __name__ == "__main__":
    main()
