#!/usr/bin/env python3
"""Generate the native zero certificates: the batches checked by compiled evaluation.

The same plan as `gen_zero_certificates.py` (same stores, same chunks, same exported
`BatchSpec n an ad bn bd` per batch), rendered for the `Native` library:

    Native/Certificates/<Method>/Shard<kkkk>.lean
        # `NATIVE_BATCHES_PER_MODULE` batches each, every one a theorem
        #   `Native.Certificates.<Method>.Batch<kkkk>.batch : BatchSpec …`
        # proved by the method's native metaprogram (`build_batch_rs +native lo hi`), which reads
        # the store rows and checks them by `native_decide` on `Native.checkTiling`; past
        # `BATCHES_PER_DIR` shards they are split into `<Method>/D<dddd>/`, as the kernel batches
    Native/Certificates/Groups/Level<L>/Group<kkkk>.lean
        # level 1: `NATIVE_MODULES_PER_GROUP` consecutive batch modules (shards, and for a method
        # with no native check its kernel-checked batch modules), folded by the same
        # `BatchSpec.append` fold as the kernel assembler into one exported
        #   `Native.Certificates.Groups.Level1.Group<kkkk>.group : BatchSpec …`;
        # each further level folds `NATIVE_MODULES_PER_GROUP` groups of the level below
    Native/Certificates.lean
        # the assembler: the same fold again, over the top level's groups
    Native/CountCertificates.lean
        # `Native.certifiedZeroCount`, as `Zeta/Zeros/CountCertificates.lean` but on the above

A module carries the fixed cost of its `Mathlib` import however few batches it holds, so batches
are packed several to a module (a shard, as in `comparator/shard.sh`: batches checked together to
share a fixed cost), and shards still build in parallel.

The fold is a tree for the same reason. A single assembler with one prefix theorem per batch is
serial, and its size grows with the batch count. Folding each group of modules in its own module
builds the groups in parallel, and levels are added until the assembler has at most
`NATIVE_MODULES_PER_GROUP` steps; every seam is still one `Nat.ble` closed by `rfl`.

A shard or group module this generator wrote earlier that this run does not rewrite (the store
shrank) is stale, and handled as `gen_zero_certificates.py` handles its own: listed, and nothing
written, unless `--prune` is passed, which removes them.

Run from the project root:
    python3 python/src/data_gen/gen_native_certificates.py Native [--prune] [<store>…]
"""
from __future__ import annotations

import argparse
import re
from collections.abc import Iterator
from dataclasses import dataclass
from itertools import groupby, islice
from pathlib import Path

from data_gen.gen_count_certificate import gen_count_certificate
from data_gen.gen_zero_certificates import (
    BATCHES_PER_DIR,
    BatchRef,
    StorePlan,
    default_stores,
    fold_levels,
    fold_name,
    gen_bundle,
    gen_fold,
    header,
    group_quals,
    iter_batches,
    module_path,
    module_qual,
    plan_stores,
    prune_or_stop,
    rel,
    stale_files,
    wrap_params,
    write_module,
)
from data_gen.lean_dialect import LeanDialect

#: batches per generated native module
NATIVE_BATCHES_PER_MODULE = 25

#: batch modules (shards, or kernel-checked batch modules) folded by one group module
NATIVE_MODULES_PER_GROUP = 25

SCRIPT = "gen_native_certificates.py"

ROOT = Path(__file__).resolve().parents[3]


def kernel_module(qual: str) -> str:
    return f"Zeta.Zeros.Certificates.{qual}"


def theorem_name(ref: BatchRef) -> str:
    """A batch's theorem as the native assembler refers to it."""
    if ref.dialect.native_metaprogram:
        return f"Native.Certificates.{ref.qual}.batch"
    return f"Zeta.Certificates.{ref.qual}.batch"


def gen_native_batch(ref: BatchRef, rows: list[list[str]]) -> str:
    """One batch's namespace and theorem."""
    dialect = ref.dialect
    lo, hi = ref.row_start, ref.row_start + len(rows)
    return f"""namespace Native.Certificates.{ref.qual}

/-- Zeta zeros #{rows[0][0]}–#{rows[-1][0]} (`t ≈ {rows[0][1][:12]} … {rows[-1][2][:12]}`), bracketed by
the {dialect.method} approximant and checked by compiled evaluation. -/
theorem batch : {ref.spec} := by
  {dialect.native_metaprogram} {lo} {hi}

end Native.Certificates.{ref.qual}
"""


def gen_shard(subdir: str, shard: int, batches: list[tuple[BatchRef, list[list[str]]]],
             params: dict, src: str) -> str:
    first, last = batches[0][0], batches[-1][0]
    note = (f"Native {subdir} shard {shard}: batches {first.bidx}–{last.bidx}, zeta zeros "
            f"#{batches[0][1][0][0]}–#{batches[-1][1][-1][0]},\nchecked by compiled evaluation "
            f"(`native_decide` on `Native.checkTiling`).\n{wrap_params(params)}")
    body = "\n".join(gen_native_batch(ref, rows) for ref, rows in batches)
    return header(src, note, SCRIPT) + f"""module

public import Native.BuildCerts

@[expose] public section

open Zeta.Certificates

{body}
end
"""


def shard_qual(subdir: str, shard: int, width: int, split: bool) -> str:
    """A shard's module relative to `Native.Certificates`, e.g. `RiemannSiegel.Shard0001`."""
    d = f".D{shard // BATCHES_PER_DIR:04d}" if split else ""
    return f"{subdir}{d}.Shard{shard:0{width}d}"


@dataclass(frozen=True)
class GroupRef:
    """A group module: consecutive batch modules (level 1) or level-(L−1) groups folded into one
    exported `BatchSpec`, which the next level or the assembler folds as `gen_fold` folds batches
    (it reads `count`, `first`, `last`, `spec`, `qual` and, through `fold_name`, `seam_tag`)."""

    level: int
    k: int
    width: int
    count: int
    first: tuple[int, int]
    last: tuple[int, int]

    @property
    def spec(self) -> str:
        return f"BatchSpec {self.count} {self.first[0]} {self.first[1]} {self.last[0]} {self.last[1]}"

    @property
    def qual(self) -> str:
        return f"Groups.Level{self.level}.Group{self.k:0{self.width}d}"

    @property
    def module(self) -> str:
        return f"Native.Certificates.{self.qual}"

    @property
    def seam_tag(self) -> str:
        return f"G{self.k:0{self.width}d}"


def group_theorem(g: GroupRef) -> str:
    return f"{g.module}.group"


def gen_group(g: GroupRef, refs: list, modules: list[str], src: str) -> str:
    """A group module: the fold of `refs` (at level 1 the batches of `modules`, above it the
    groups), exported as `group`. Only level 1 imports its children publicly, to bound the closure
    of everything above it: see `gen_group` in `gen_zero_certificates.py`."""
    imp = "public import" if g.level == 1 else "import"
    imports = "\n".join(f"{imp} {m}" for m in modules)
    kind, name = ("batches", theorem_name) if g.level == 1 else ("groups", group_theorem)
    note = (f"Native level-{g.level} group {g.k}: the {kind}\n{refs[0].qual}–{refs[-1].qual}\n"
            "folded into one `BatchSpec` by the same `BatchSpec.append` fold as\n"
            "`Zeta/Zeros/Certificates.lean`; the next level, or the assembler\n"
            "`Native/Certificates.lean`, folds the groups in turn.")
    return header(src, note, SCRIPT) + f"""module

public import Zeta.Zeros.Certificates.Fold
{imports}

@[expose] public section

namespace {g.module}

open Zeta.Certificates

{gen_fold(refs, name)}

/-- The zeros of every batch in this group:
{refs[0].qual}–{refs[-1].qual}. -/
theorem group : {g.spec} :=
  {fold_name(refs[-1])}

end {g.module}

end
"""


def gen_native_assembler(groups: list[GroupRef], src: str) -> str:
    imports = "\n".join(f"import {g.module}" for g in groups)
    note = ("Assembles the native batches (and the kernel-checked ones of methods with no native\n"
            "check) into one `BatchSpec`, by the same `BatchSpec.append` fold as\n"
            "`Zeta/Zeros/Certificates.lean`, over the groups' statements (each group folds its\n"
            "own batches). Every native batch's proof is a `native_decide`, so the result trusts\n"
            "the Lean compiler as well as the kernel.")
    return header(src, note, SCRIPT) + f"""module

public import Zeta.Zeros.Certificates.Fold
{imports}

@[expose] public section

namespace Native.Certificates

open Zeta.Certificates

{gen_fold(groups, group_theorem)}

{gen_bundle(groups)}

end Native.Certificates

end
"""


def usage(script: str) -> str:
    return (
        f"usage: {script} <native_root> [--prune] [<store>…]\n"
        "  stores default to every store under python/out/, as gen_zero_certificates.py;\n"
        "  the kernel-checked modules of methods with no native check must already be generated."
    )


def main() -> None:
    ap = argparse.ArgumentParser(usage=usage(SCRIPT).removeprefix("usage: "))
    ap.add_argument("native_root", type=Path)
    ap.add_argument("stores", nargs="*", type=Path)
    ap.add_argument("--prune", action="store_true",
                    help="delete shard and group modules generated earlier that this run does "
                         "not rewrite")
    ap.add_argument("--ignore-style", action="store_true",
                    help="allow lines past the 100-column limit (long `--no-widen` endpoints)")
    args = ap.parse_args()
    native_root = args.native_root
    style = args.ignore_style
    stores = args.stores or default_stores()
    plan = plan_stores(stores)
    srcs = ", ".join(str(p.store) for p in plan)
    cert_dir = native_root / "Certificates"

    for p in plan:
        for bidx in range(1, p.batches + 1) if not p.dialect.native_metaprogram else ():
            path = ROOT / (kernel_module(p.qual(bidx)).replace(".", "/") + ".lean")
            if not path.exists():
                raise SystemExit(f"{path} is missing: run gen_zero_certificates.py first (a native "
                                 f"build keeps the kernel-checked {p.dialect.method} batches)")
    # consecutive stores of one method share its shards, so each method's must be consecutive
    runs = [(d, list(ps)) for d, ps in groupby(plan, key=lambda p: p.dialect)]
    if len({d.subdir for d, _ in runs}) != len(runs):
        raise SystemExit("batch modules do not cover the plan in order")
    #: each native method's number of shards, by subdirectory
    n_shards = {d.subdir: -(-sum(p.batches for p in ps) // NATIVE_BATCHES_PER_MODULE)
                for d, ps in runs if d.native_metaprogram}
    n_native = sum(p.batches for p in plan if p.dialect.native_metaprogram)
    n_kernel = sum(p.batches for p in plan) - n_native
    n_units = sum(n_shards.values()) + n_kernel

    def shard(subdir: str, k: int) -> str:
        n = n_shards[subdir]
        return shard_qual(subdir, k, max(4, len(str(n))), n > BATCHES_PER_DIR)

    def keep_shard(path: Path) -> bool:
        qual = module_qual(cert_dir, path)
        subdir, m = qual.split(".")[0], re.search(r"\.Shard(\d+)$", qual)
        k = int(m[1]) if m else 0
        return 1 <= k <= n_shards[subdir] and qual == shard(subdir, k)

    shard_dirs = [d for s in n_shards for d in (cert_dir / s, *(cert_dir / s).glob("D*"))]
    group_dir = cert_dir / "Groups"
    groups = set(group_quals(n_units, NATIVE_MODULES_PER_GROUP, GroupRef))
    prune_or_stop(stale_files(shard_dirs, "Shard*.lean", keep_shard, SCRIPT)
                  + stale_files([group_dir, *group_dir.glob("Level*")], "Group*.lean",
                                lambda f: module_qual(cert_dir, f) in groups, SCRIPT),
                  args.prune, SCRIPT)

    def write_shards(dialect: LeanDialect, stores: list[StorePlan]
                     ) -> Iterator[tuple[str, list[BatchRef]]]:
        """A method's batch modules with the batches each holds, its shards written as they fill."""
        batches = iter_batches(stores)
        if not dialect.native_metaprogram:
            yield from ((kernel_module(ref.qual), [ref]) for ref, _, _, _ in batches)
            return
        k = 0
        while chunk := list(islice(batches, NATIVE_BATCHES_PER_MODULE)):
            k += 1
            qual = shard(dialect.subdir, k)
            srcs_k = ", ".join(dict.fromkeys(str(i[3]) for i in chunk))
            text = gen_shard(dialect.subdir, k, [(i[0], i[1]) for i in chunk], chunk[-1][2], srcs_k)
            write_module(module_path(cert_dir, qual), text, style)
            yield f"Native.Certificates.{qual}", [i[0] for i in chunk]

    def write_group(g: GroupRef, children: list, modules: list[str]) -> None:
        write_module(module_path(cert_dir, g.qual), gen_group(g, children, modules, srcs), style)

    # runs of consecutive modules fold into level-1 groups, those into a tree, the top level's
    # groups in the assembler; a level-1 group's children are the batches of its modules
    units = (unit for d, ps in runs for unit in write_shards(d, ps))
    level1: list[GroupRef] = []
    width = max(4, len(str(-(-n_units // NATIVE_MODULES_PER_GROUP))))
    while chunk := list(islice(units, NATIVE_MODULES_PER_GROUP)):
        refs = [r for _, rs in chunk for r in rs]
        level1.append(GroupRef(1, len(level1) + 1, width, sum(r.count for r in refs),
                               refs[0].first, refs[-1].last))
        write_group(level1[-1], refs, [m for m, _ in chunk])
    levels = fold_levels([(g, []) for g in level1], NATIVE_MODULES_PER_GROUP, GroupRef)
    for level in levels[1:]:
        for g, children in level:
            write_group(g, children, [c.module for c in children])
    write_module(native_root / "Certificates.lean",
                 gen_native_assembler([g for g, _ in levels[-1]], srcs), style)

    unfolds = "".join(", " + u for u in plan[-1].dialect.seam_unfold)
    zsrc = "\n".join(f"  {rel(str(s))}" for s in stores)
    write_module(native_root / "CountCertificates.lean",
                 gen_count_certificate(unfolds, zsrc, native=True), style)

    print(f"wrote {n_native} native batches in {sum(n_shards.values())} modules, "
          f"{n_kernel} kernel batches reused, "
          f"{' + '.join(str(len(level)) for level in levels)} groups ({len(levels)} "
          f"level{'s' * (len(levels) > 1)}), + assembler and count certificate under {native_root}")


if __name__ == "__main__":
    main()
