import json
import argparse
import shutil
from collections.abc import Iterable
from pathlib import Path

from config import OUT_DIR, DIGITS, IMPORT_DP, ROWS_PER_FILE
from approximants import build_approx, method_subparsers
from util import ZApproximant, ZInterval
from search import ZeroSearch

def zeros_file(k: int) -> str:
    """The name of a store's `k`-th file (1-based)."""
    return f"zeros_{k:05d}.txt"


def trim(field: str) -> str:
    """A decimal field without the trailing zeros of the fixed-width format, keeping at least
    `IMPORT_DP` fractional digits. Boundaries are placed at `IMPORT_DP` places or more (see
    `ZInterval.place_boundary`), so this keeps every digit they were placed at: Lean and the
    generator read the endpoint exactly as written."""
    i, dot, f = field.partition(".")
    if not dot:
        return field
    return f"{i}.{f.rstrip('0').ljust(IMPORT_DP, '0')}"


def write_rows(rows: list[tuple[int, ZInterval]], out: str, digits: int = DIGITS):
    out = Path(out).expanduser()
    out.parent.mkdir(parents=True, exist_ok=True)
    with open(out, "w") as f:
        body = "".join(f"{i}, {z.row(digits)}\n" for i, z in rows)
        f.write(body)


def write_store(
    out: Path, lines: Iterable[str], cols, params: dict, rows_per_file: int = ROWS_PER_FILE
) -> dict:
    """Write a zero store: `lines` (`idx, left, right, …`, ascending) split into files of
    `rows_per_file` rows as they arrive, plus the `manifest.json` indexing them. The files are
    staged in `.partial/` and moved into place only once `lines` is exhausted, so a run that
    fails part-way leaves the previous store intact. Store files of an earlier run that this one
    does not rewrite are removed, so the manifest is the whole store."""
    out = Path(out).expanduser()
    partial = out / ".partial"
    shutil.rmtree(partial, ignore_errors=True)
    partial.mkdir(parents=True)
    files = []

    def flush(rows: list[str]):
        name = zeros_file(len(files) + 1)
        (partial / name).write_text("".join(f"{line}\n" for line in rows))
        files.append({"file": name, "rows": len(rows), "height": rows[-1].split(",")[2].strip()})

    rows = []
    for line in lines:
        rows.append(", ".join(trim(c.strip()) for c in line.split(",")))
        if len(rows) == rows_per_file:
            flush(rows)
            rows = []
    if rows:
        flush(rows)
    for f in files:
        (partial / f["file"]).replace(out / f["file"])
    partial.rmdir()
    keep = {f["file"] for f in files}
    for stale in [*out.glob("zeros_*.txt"), out / "zeros.txt"]:
        if stale.is_file() and stale.name not in keep:
            stale.unlink()
    manifest = {
        "rows": sum(f["rows"] for f in files),
        "rows_per_file": rows_per_file,
        "height": files[-1]["height"] if files else None,
        "cols": list(cols),
        "params": params,
        "files": files,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def store_zeros(
    start: float,
    end: float,
    approx: ZApproximant,
    bisection_depth: int,
    epsilon: float = 1 / 4,
    verbose: bool = False,
    widen: bool = False,
    num_workers: int = 1,
    window_retries: int = 100,
    halving_depth: int = 10,
    rows_per_file: int = ROWS_PER_FILE,
):
    search = ZeroSearch(approx, bisection_depth, epsilon, widen, window_retries, halving_depth)
    zeros = search.iter_zeros(start, end, verbose, num_workers)
    params = approx.metadata() | {
        "bisection_depth": bisection_depth,
        "epsilon": epsilon,
        "widen": widen,
        "window_retries": window_retries,
        "halving_depth": halving_depth,
    }
    return write_store(
        f"{OUT_DIR}/{approx.name}/zeros",
        (f"{i}, {z.row(DIGITS)}" for i, z in enumerate(zeros, start=1)),
        ("idx",) + approx.row_cols,
        params,
        rows_per_file,
    )


def zeros_flags():
    p = argparse.ArgumentParser(add_help=False)
    p.add_argument("start", type=float, help="lower height bound")
    p.add_argument("end", type=float, help="upper height bound")
    s = p.add_argument_group("zero store")
    s.add_argument(
        "--widen",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="widen intervals maximally into a tiling, each boundary at the fewest decimal "
        "places that work; Lean reads endpoints as written, so --no-widen stores import at "
        "full precision (default: %(default)s)",
    )
    s.add_argument(
        "--num-workers",
        type=int,
        metavar="N",
        help="number of worker processes for the search; -1 (the default) uses every core. "
        "Pass a small number on a shared login node",
        default=-1,
    )
    s.add_argument(
        "--window-retries",
        type=int,
        default=100,
        metavar="N",
        help="how many times the search of a Rosser block whose zeros do not all show is "
        "retried on a window grown by one block before it gives up (default: %(default)s)",
    )
    s.add_argument(
        "--halving-depth",
        type=int,
        default=10,
        metavar="N",
        help="how many times a Rosser block whose zeros do not all show is refined "
        "(its Gram intervals halved) before it counts as failed (default: %(default)s)",
    )
    s.add_argument(
        "--rows-per-file",
        type=int,
        default=ROWS_PER_FILE,
        metavar="N",
        help="rows per store file; the store is split so no file nears GitHub's size limit "
        "(default: %(default)s)",
    )
    return p


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Find and store critical-line zero brackets of ζ in [start, end] "
        "(candidates for the Lean certificates; not themselves rigorous)."
    )
    method_subparsers(parser, parents=[zeros_flags()])
    args = parser.parse_args()
    approx = build_approx(args)
    store_zeros(
        args.start,
        args.end,
        approx,
        args.bisection_depth,
        args.epsilon,
        args.verbose,
        args.widen,
        num_workers=args.num_workers,
        window_retries=args.window_retries,
        halving_depth=args.halving_depth,
        rows_per_file=args.rows_per_file,
    )
    print(f"stored zeros in [{args.start}, {args.end}] -> {OUT_DIR}/{approx.name}/zeros/")
