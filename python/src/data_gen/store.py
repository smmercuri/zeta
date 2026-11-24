import argparse
import json
from decimal import ROUND_FLOOR, Decimal
from pathlib import Path

from config import OUT_DIR
from approximants import build_approx, method_subparsers
from data_gen.store_gram import gram_opts, store_gram
from data_gen.store_zeros import zeros_flags, store_zeros

#: imaginary part of the first nontrivial zero; below it there is nothing to count
FIRST_ZERO = 14.13


def zeros_below(start: float) -> int | None:
    """How many critical-line zeros lie below `start`, for the Turing count check.

    Zero if `start` is below the first zero. Otherwise the zeros below `start` are some other
    store's (the Euler–Maclaurin one at low height), so its row count is read off its manifest,
    provided that store searched up to exactly `start` (older manifests record only `height`,
    where its last interval ends). `None` when no such store is found, in which case the count
    cannot be checked here."""
    if start < FIRST_ZERO:
        return 0
    for manifest in Path(OUT_DIR).expanduser().glob("*/zeros/manifest.json"):
        m = json.loads(manifest.read_text())
        top = m.get("end", m["height"])
        if top is not None and abs(Decimal(str(top)) - Decimal(str(start))) < Decimal("1e-9"):
            return int(m["rows"])
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Find and store a good Gram block above `end` and brackets for the "
        "critical-line zeros of ζ up to its lower gram point (candidates for the Lean "
        "certificates; not themselves rigorous)."
    )
    method_subparsers(parser, parents=[zeros_flags(), gram_opts()])
    args = parser.parse_args()
    approx = build_approx(args)

    # The gram block first: Turing's bound is stated at its lower gram point `g_N`, so the zero
    # bundle must tile `[start, g_N]` exactly: every zero below `g_N` counted, none above it.
    # Searching only to `end` and then looking for a block above it would drop the zeros in
    # `(end, g_N)`.
    bl = store_gram(
        args.end,
        approx,
        args.bisection_depth,
        args.lc,
        args.gram_cap,
        args.epsilon,
    )
    print(
        f"stored gram block g_{bl.lower}..g_{bl.upper} -> {OUT_DIR}/{approx.name}/gram/"
    )

    # The top edge is `g_N` floored to 3 decimals (`IMPORT_DP`), the precision it is stored and
    # imported at: the bundle's height must not round *above*
    # `g_N`. A zero within 0.0005 of `g_N` would then be left out, and the count check
    # below reports it.
    top = float(
        Decimal(str(bl.gram_lower)).quantize(Decimal("0.001"), rounding=ROUND_FLOOR)
    )
    manifest = store_zeros(
        args.start,
        top,
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
    print(f"stored zeros in [{args.start}, {top}] -> {OUT_DIR}/{approx.name}/zeros/")
    stored = manifest["rows"]

    # Turing: `N(g_N) ≤ N + 1`; this store plus whatever lies below `start` must supply exactly
    # that many zeros, or the Lean count certificate fails.
    below = zeros_below(args.start)
    if below is None:
        print(
            f"count check skipped: no store ends at {args.start}, so the zeros below it are "
            f"unknown here (Turing allows {bl.lower + 1} below g_{bl.lower} in total)"
        )
    elif stored + below != bl.lower + 1:
        raise SystemExit(
            f"count mismatch: {stored} zeros stored in [{args.start}, {top}] plus {below} "
            f"below {args.start} is {stored + below}, but Turing's bound allows "
            f"{bl.lower + 1} below g_{bl.lower}; the Lean count certificate would fail"
        )
    else:
        print(
            f"count check: {stored} + {below} below {args.start} = g_{bl.lower} index + 1"
        )
