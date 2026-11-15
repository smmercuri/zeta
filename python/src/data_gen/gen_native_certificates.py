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
from dataclasses import dataclass
from pathlib import Path

from data_gen.gen_count_certificate import gen_count_certificate
from data_gen.gen_zero_certificates import (
    BATCHES_PER_DIR,
    BatchRef,
    chunk_groups,
    default_stores,
    fold_levels,
    fold_name,
    gen_bundle,
    gen_fold,
    header,
    module_path,
    plan_batches,
    prune_or_stop,
    rel,
    stale_files,
    wrap_params,
    write_module,
)

#: batches per generated native module
NATIVE_BATCHES_PER_MODULE = 25

#: batch modules (shards, or kernel-checked batch modules) folded by one group module
NATIVE_MODULES_PER_GROUP = 25

SCRIPT = "gen_native_certificates.py"

ROOT = Path(__file__).resolve().parents[3]


def kernel_module(ref: BatchRef) -> str:
    return f"Zeta.Zeros.Certificates.{ref.qual}"


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
    plan = plan_batches(stores)

    #: every batch module with the batches it holds, sorted into plan order below
    units: list[tuple[str, list[BatchRef]]] = []
    native = [item for item in plan if item[0].dialect.native_metaprogram]
    for ref, _, _, _ in plan:
        if not ref.dialect.native_metaprogram:
            path = ROOT / (kernel_module(ref).replace(".", "/") + ".lean")
            if not path.exists():
                raise SystemExit(f"{path} is missing: run gen_zero_certificates.py first (a native "
                                 f"build keeps the kernel-checked {ref.dialect.method} batches)")
            units.append((kernel_module(ref), [ref]))
    # pack each method's native batches, in order, into shards
    by_dir: dict[str, list] = {}
    for item in native:
        by_dir.setdefault(item[0].dialect.subdir, []).append(item)
    #: each shard's path, method subdirectory, number and batches
    shards: list[tuple[Path, str, int, list]] = []
    cert_dir = native_root / "Certificates"
    for subdir, items in by_dir.items():
        chunks = [items[i:i + NATIVE_BATCHES_PER_MODULE]
                  for i in range(0, len(items), NATIVE_BATCHES_PER_MODULE)]
        width, split = max(4, len(str(len(chunks)))), len(chunks) > BATCHES_PER_DIR
        for k, chunk in enumerate(chunks, start=1):
            qual = shard_qual(subdir, k, width, split)
            shards.append((module_path(cert_dir, qual), subdir, k, chunk))
            units.append((f"Native.Certificates.{qual}", [i[0] for i in chunk]))

    refs = [p[0] for p in plan]
    srcs = ", ".join(dict.fromkeys(str(p[3]) for p in plan))
    position = {ref: i for i, ref in enumerate(refs)}
    units.sort(key=lambda u: position[u[1][0]])
    if [r for _, rs in units for r in rs] != refs:
        raise SystemExit("batch modules do not cover the plan in order")
    # runs of consecutive modules fold into level-1 groups, those into a tree, the top level's
    # groups in the assembler; a level-1 group's children are the batches of its modules
    unit_chunks = [units[i:i + NATIVE_MODULES_PER_GROUP]
                   for i in range(0, len(units), NATIVE_MODULES_PER_GROUP)]
    level1 = chunk_groups(1, [[r for _, rs in chunk for r in rs] for chunk in unit_chunks], GroupRef)
    modules = {g: [m for m, _ in chunk] for (g, _), chunk in zip(level1, unit_chunks)}
    levels = fold_levels(level1, NATIVE_MODULES_PER_GROUP, GroupRef)

    written: dict[Path, set[Path]] = {}
    for d in by_dir:
        for dd in (cert_dir / d, *(cert_dir / d).glob("D*")):
            written.setdefault(dd, set())
    for path, _, _, _ in shards:
        written.setdefault(path.parent, set()).add(path)
    group_dir = cert_dir / "Groups"
    group_written: dict[Path, set[Path]] = {d: set() for d in (group_dir, *group_dir.glob("Level*"))}
    for level in levels:
        for g, _ in level:
            path = module_path(cert_dir, g.qual)
            group_written.setdefault(path.parent, set()).add(path)
    prune_or_stop(stale_files(written, "Shard*.lean", SCRIPT)
                  + stale_files(group_written, "Group*.lean", SCRIPT), args.prune, SCRIPT)

    for path, subdir, k, chunk in shards:
        srcs_k = ", ".join(dict.fromkeys(str(i[3]) for i in chunk))
        text = gen_shard(subdir, k, [(i[0], i[1]) for i in chunk], chunk[-1][2], srcs_k)
        write_module(path, text, style)

    for level in levels:
        for g, children in level:
            imports = modules[g] if g.level == 1 else [c.module for c in children]
            write_module(module_path(cert_dir, g.qual), gen_group(g, children, imports, srcs),
                         style)
    groups = [g for g, _ in levels[-1]]
    write_module(native_root / "Certificates.lean", gen_native_assembler(groups, srcs), style)

    last_ref = refs[-1]
    unfolds = "".join(", " + u for u in last_ref.dialect.seam_unfold)
    zsrc = "\n".join(f"  {rel(str(s))}" for s in stores)
    write_module(native_root / "CountCertificates.lean",
                 gen_count_certificate(unfolds, zsrc, native=True), style)

    n_native = len(native)
    print(f"wrote {n_native} native batches in {len(shards)} modules, "
          f"{len(refs) - n_native} kernel batches reused, "
          f"{' + '.join(str(len(level)) for level in levels)} groups ({len(levels)} "
          f"level{'s' * (len(levels) > 1)}), + assembler and count certificate under {native_root}")


if __name__ == "__main__":
    main()
