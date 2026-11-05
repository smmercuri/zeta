#!/usr/bin/env python3
"""Generate `Zeta/Gram/Certificates.lean` from a gram-block *store directory*.

The store (default `python/out/euler_maclaurin/gram`) is written by
`data_gen/store_gram.py` from `gram_points.get_good_gramBlock`, and holds one gram
block across three kinds of file:

`manifest.json`
    `height`, `Lehman constant`, `cols`, `params` (`bisection_depth`, `epsilon`, `b`,
    `prec`), and `zeros_map`, which maps each block's lower gram index to that
    block's zero file.  `zeros_map` is the authoritative list of zero files.

`gram_block.txt`
    One row per gram point — a *flat* list in increasing index order, so `k` blocks
    are described by `k+1` rows — with seven comma-separated fields

        idx, lower, upper, lower_cutoff, upper_cutoff, lower_bernoulli, upper_bernoulli

    bracketing the `idx`-th gram point in `[lower, upper]` and carrying the theta Stirling
    shift/order used to certify it at each endpoint.  `parse_gram_points`
    reorders these into the endpoint-paired `GramPt` layout `(idx, lo, hi, lc, lb,
    rc, rb)` that `GramPoint` expects.  Blocks are then formed by `build_blocks`,
    pairing each consecutive row with its successor.

`zeros_<idx>.txt`
    One row per bracketed zero lying between `g_idx` and `g_idx+1`, with seven fields

        idx, left, right, leftCutoff, rightCutoff, leftBernoulli, rightBernoulli

    The leading ordinal is dropped to give the six-field `ZeroInterval` layout, exactly
    as in `gen_zero_certificates.py`.  These are located through `zeros_map`, falling
    back to the `zeros_<idx>.txt` naming convention when an index is absent from it.

Both parsers skip lines that do not begin with a digit, and rows of the wrong arity, so
a free-form header is tolerated in either file (`store_gram.py` writes none).

Because the blocks tile consecutively, adjacent blocks share a gram point (block `k`'s
right endpoint is block `k+1`'s left endpoint).  We therefore emit each gram point in
`gram_block.txt` exactly once — as `gp1, gp2, …` with one `Certificate` apiece — and let
each block reference the shared `gp{k}`/`gp{k+1}` rather than redefining and re-certifying
`gpL`/`gpR` per block.  We then emit one `ZeroInterval`/`Certificate` per contained zero, a
`GramBlock`/`Certificate` per block, and finally one `CertifiedGramBlockSeq` bundling every
block with the chain, Lehman `wide`, and `168π` height obligations.

Everything numeric and *decidable* (`fst_le_snd`, `_nonneg`, the `_pos` fields, the
`seq` index arithmetic, the `IsChain`, list membership, `contains_zero`) is
discharged by `norm_num` / `decide` / `fin_cases`.  The obligations needing rigorous
transcendental enclosures are handled as follows:

  * gram points : `fst_bound`, `snd_bound` — `gram_bound`.  Bracketing a gram point is a
    question about `theta` alone, so this is method-independent and always discharged.
  * zeros       : `is_sign_change`, `fst_error`, `snd_error` — `hardy_sign_change` /
    `hardy_error_ok_full` when the store's dialect `proves_obligations` (Euler-Maclaurin);
    `sorry` otherwise (Riemann-Siegel, pending the engine's generalisation).
  * sequence    : `wide` (needs `Real.log`/`π` bounds), `high` (needs a `π` bound) — emitted
    as `sorry` when the data is out of range.

The store carries the approximant's parameters for the zeros and the theta Stirling
shift/order for the gram points, so they are read straight from it and never recomputed here.
The working precision is read from `manifest["params"]` purely to record it in the
generated file's provenance header; `gen_wide` and `gen_high` derive their bounds
from the bracket endpoints alone.

Run from the project root (output first, store second, as the other generators):
    python3 python/src/data_gen/gen_gram_certificates.py \
        Zeta/Gram/Certificates.lean python/out/riemann_siegel/gram
"""
from __future__ import annotations

import json
import math
import sys
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal, getcontext
from pathlib import Path

from config import (
    LEHMAN_CONST,
    LEHMAN_LOG_COEFF,
    LEHMAN_MIN_HEIGHT_PI,
    PI_LOWER,
    PI_UPPER,
    GRAM_WIDEN_DP,
)
from data_gen.gen_zero_certificates import write_module
from data_gen.lean_dialect import LeanDialect, dialect_for

# --- parsing -----------------------------------------------------------------

# A gram point is one data line of seven fields in the grouped layout (matching the
# zero lines and the file's column header):
#   idx, lower, upper, lower_cutoff, upper_cutoff, lower_bernoulli, upper_bernoulli
# We reorder them into the `GramPt` layout below — shift/order paired per endpoint,
# as `GramPoint` expects — so the lower-endpoint pair feeds `fstVal` and the
# upper-endpoint pair `sndVal`.  Nothing is recomputed; the pipeline emits the theta
# Stirling parameters directly (`store_gram.theta_params_rule`).
# The store's gram brackets are refined to ~1e-27, which certifies nothing in Lean: the
# `gram_bound` enclosure runs at working precision `D = 1e8·(t/30)`, i.e. a resolution of
# ~2e-10 at t ≈ 1420, so a margin that small is invisible to it. We therefore widen each
# bracket outward before emitting it. This is always sound — the interval still contains the
# gram point — and it strictly *increases* both certificate margins, since `fst_bound` is
# `idx·π − θ(fst)` (bigger as `fst` drops) and `snd_bound` is `θ(snd) − idx·π` (bigger as `snd`
# rises). It is the same trade the zero brackets make by being stored at few decimal places
# (`IMPORT_DP` in `config.py`).
getcontext().prec = 80



def widen_down(s: str) -> str:
    """Largest `GRAM_WIDEN_DP`-place decimal that is at least `10^-GRAM_WIDEN_DP` *below* `s`.

    Rounding to the grid alone is not enough: if `s` sits just above a grid point the margin
    would still be ~0, so we take a further whole ulp."""
    q = Decimal(1).scaleb(-GRAM_WIDEN_DP)
    return str(Decimal(s).quantize(q, rounding=ROUND_FLOOR) - q)


def widen_up(s: str) -> str:
    """Smallest `GRAM_WIDEN_DP`-place decimal at least `10^-GRAM_WIDEN_DP` *above* `s`."""
    q = Decimal(1).scaleb(-GRAM_WIDEN_DP)
    return str(Decimal(s).quantize(q, rounding=ROUND_CEILING) + q)


GramPt = tuple  # (idx, lo, hi, lc, lb, rc, rb)
Block = dict  # {"left": GramPt, "right": GramPt, "zeros": list[tuple[str, ...]]}


def parse_gram_points(path: Path) -> list[GramPt]:
    """`gram_block.txt`: one 7-field row per gram point,
    `idx, lo, hi, lower_cutoff, upper_cutoff, lower_bernoulli, upper_bernoulli`.
    Reordered into the endpoint-paired `GramPt` layout `(idx, lo, hi, lc, lb, rc, rb)`."""
    pts: list[GramPt] = []
    for line in path.read_text().splitlines():
        s = line.strip()
        if not s or not s[0].isdigit():
            continue
        parts = [p.strip() for p in s.split(",")]
        if len(parts) != 7:
            continue
        idx, lo, hi, lc, rc, lb, rb = parts
        # Widen here rather than at emission, so the block gaps, `separated` and
        # `contains_zero` are all computed against the brackets that actually get emitted.
        pts.append((idx, widen_down(lo), widen_up(hi), lc, lb, rc, rb))
    return pts


def parse_zeros(path: Path, dialect: LeanDialect) -> list[list[str]]:
    """`zeros_<idx>.txt`: the block's bracketed zeros, in the store's `zero_cols` layout.

    The leading ordinal is kept: the dialect renders a row whole, exactly as it does for
    `gen_zero_certificates`."""
    rows: list[list[str]] = []
    if not path.exists():
        return rows
    for line in path.read_text().splitlines():
        s = line.strip()
        if not s or not s[0].isdigit():
            continue
        parts = [p.strip() for p in s.split(",")]
        if len(parts) != dialect.row_width:
            continue
        dialect.check_row(path, parts)
        rows.append(parts)
    return rows


def build_blocks(gram_pts: list[GramPt], store: Path, manifest: dict,
                 dialect: LeanDialect) -> list[Block]:
    """Pair consecutive gram points into blocks and attach each block's zeros
    (`zeros_map` keys the file by the block's lower gram index).

    A block's `left`/`right` are the *shared* gram-point tuples from `gram_pts`: the
    right gram point of block `k` is the same object as the left gram point of block
    `k+1` (both `gram_pts[k+1]`).  The emitter exploits this to define and certify each
    gram point once (see `gen_gram_points`)."""
    zmap = manifest.get("zeros_map", {})
    blocks: list[Block] = []
    for k in range(len(gram_pts) - 1):
        left, right = gram_pts[k], gram_pts[k + 1]
        gram_idx = left[0]
        zfile = zmap.get(str(gram_idx), f"zeros_{gram_idx}.txt")
        blocks.append(
            {"left": left, "right": right, "zeros": parse_zeros(store / zfile, dialect)})
    return blocks


def gram_point_name(k: int) -> str:
    """Name of the `k`-th gram point (1-indexed) in the flat `gram_block.txt` list."""
    return f"gp{k}"


# --- Lean emission -----------------------------------------------------------


def gen_gram_point(name: str, idx: str, g: GramPt) -> str:
    """A `GramPoint` and its certificate.

    Method-agnostic: the parameters are the *theta* Stirling orders from `gram_block.txt`,
    which the gram store writes whichever approximant certified the zeros."""
    _, lo, hi, lc, lb, rc, rb = g
    return f"""abbrev {name} : GramPoint where
  idx := {idx}
  fst := {lo}
  snd := {hi}
  fst_le_snd := by norm_num
  fstCutoff := {lc}
  fstBernoulli := {lb}
  sndCutoff := {rc}
  sndBernoulli := {rb}

theorem {name}_cert : {name}.Certificate where
  fst_nonneg := by norm_num
  snd_nonneg := by norm_num
  fstBernoulli_pos := by norm_num
  sndBernoulli_pos := by norm_num
  fst_bound := by gram_bound
  snd_bound := by gram_bound
"""


def gen_zero(name: str, row: list[str], dialect: LeanDialect) -> str:
    """A bracketed zero and its certificate, in whichever dialect the store was written."""
    return f"{dialect.interval_block(name, row)}\n{dialect.certificate_block(name, row)}"


def gen_gram_points(gram_pts: list[GramPt]) -> str:
    """Emit one `GramPoint` abbrev + `Certificate` per row of `gram_block.txt`.

    Blocks tile consecutively, so the interior gram points are shared between adjacent
    blocks (block `k`'s right endpoint is block `k+1`'s left endpoint).  Defining each
    gram point once here — rather than re-emitting `gpL`/`gpR` per block — halves the
    gram-point definitions and their `sorry`-carrying certificates."""
    return "\n".join(
        gen_gram_point(gram_point_name(k), g[0], g)
        for k, g in enumerate(gram_pts, start=1))


def gen_block(i: int, block: Block, dialect: LeanDialect) -> str:
    """Emit block `i`'s zeros and its `GramBlock`/`Certificate`.  The block references the
    shared gram points `gp{i}` (left) and `gp{i+1}` (right) emitted by `gen_gram_points`."""
    gpl, gpr = gram_point_name(i), gram_point_name(i + 1)
    zs = block["zeros"]
    znames = [f"z{i}_{j}" for j in range(1, len(zs) + 1)]
    zero_list = "[" + ", ".join(dialect.interval_ref(zn) for zn in znames) + "]"

    parts = [gen_zero(zn, row, dialect) for zn, row in zip(znames, zs)]

    # `has_zero` is the *consequence* of a certificate, not the certificate: the block records
    # that each interval brackets a zero, so it is indifferent to which method established it.
    zero_bullets = "\n".join(
        f"    · exact {dialect.exists_zero_term(zn)}" for zn in znames)

    # The inner gap `[gpL.right, gpR.left] ⊆ [gₙ, gₙ₊₁]`.  Pick the first zero whose bracket sits
    # inside it as the existential witness for `contains_zero`; if none does (e.g. unrefined,
    # `bisection_depth = 0` data where a zero's bracket still touches a gram point) fall back
    # to `sorry`.
    # Compare against the *widened* bounds, which are what the emitted `gpL`/`gpR` carry --
    # not the store's exact ones.  Widening moves `gpL.snd` up and `gpR.fst` down, so the gap
    # Lean sees is strictly narrower than the store's; checking the store's gap would accept a
    # witness whose `norm_num` membership goals are false.
    gap_lo, gap_hi = Decimal(widen_up(block["left"][2])), Decimal(widen_down(block["right"][1]))
    witness = next(
        (zn for zn, row in zip(znames, zs)
         if gap_lo <= Decimal(row[1]) and Decimal(row[2]) <= gap_hi),
        None)
    if witness is not None:
        contains = (f"  contains_zero := ⟨{witness}, by simp, "
                    f"by norm_num [Set.mem_Icc], by norm_num [Set.mem_Icc]⟩")
    else:
        contains = ("  -- No contained zero on this (unrefined) data: every zero's bracket still\n"
                    "  -- touches a gram bracket, so none fits the inner gap. Refine the zeros\n"
                    "  -- (`bisection_depth > 0`) and regenerate to discharge this.\n"
                    "  contains_zero := sorry")

    parts.append(f"""abbrev blk{i} : GramBlock where
  left := {gpl}
  right := {gpr}
  zeros := {zero_list}
  seq := by norm_num
  separated := by norm_num

theorem blk{i}_cert : blk{i}.Certificate where
  left_certificate := {gpl}_cert
  right_certificate := {gpr}_cert
  has_zero := by
    intro z hz
    fin_cases hz
{zero_bullets}
{contains}
""")
    return "\n".join(parts)


#: Rational lower bound for `e` used to certify `log` bounds (`Real.exp_one_gt_d9` covers it).
#: Must be tight enough that `E^p` beats `x^q`; `2.7` is not, once `p` is large.
LOG_BASE = 2.718

#: Largest denominator tried when fitting a rational bound `p/q` to `log`. Each step of `q`
#: refines the bound by `1/q`, so a handful of values already beats the integer bound by an
#: order of magnitude.
MAX_LOG_DENOM = 20


def gen_wide(blocks: list[Block]) -> str:
    """Proof of `wide` — an elementary `π`/`log` inequality (no ζ values, no ball arithmetic).

    Let `a = last.right.right`, `RHS = (last.right.left - first.left.right)/2`. We must show
    `LEHMAN_CONST + LEHMAN_LOG_COEFF·log(a/2π) < RHS`. Upper-bound `a/2π` by the rational
    `x = a/(2·PI_LOWER)` using `π > PI_LOWER`, then bound `log x` by any rational `p/q` in
    `(log x, (RHS - LEHMAN_CONST)/LEHMAN_LOG_COEFF)`: from
    `x^q < E^p ≤ e^p` (with `E` a rational lower bound for `e`) we get `q·log x < p`, and
    `nlinarith` finishes.

    `q = 1` is the integer bound this used to be limited to, which fails whenever the Lehman
    margin is under `LEHMAN_LOG_COEFF` — the slack left over by `get_wide_gramBlock` is a fraction of a
    gram step, so that happens regularly and increasingly often as the height grows. Falls back
    to `sorry` only when no `p/q` with `q ≤ MAX_LOG_DENOM` fits.
    """
    n = len(blocks)
    # Reference the gram-point abbrevs (defeq to the goal's `getLast`/`head` projections)
    # rather than inlining the 40-digit literals — keeps the `show`/`have` lines short.
    # The last block's right endpoint is gram point `n+1`; the first block's left is `gp1`.
    last, first = gram_point_name(n + 1), gram_point_name(1)
    aN, rlN, frN = f"{last}.snd", f"{last}.fst", f"{first}.snd"
    a = blocks[-1]["right"][2]
    rl = blocks[-1]["right"][1]
    fr = blocks[0]["left"][2]
    rhs = (float(rl) - float(fr)) / 2
    x_ub = float(a) / (2 * float(PI_LOWER))
    hi = (rhs - LEHMAN_CONST) / LEHMAN_LOG_COEFF  # any log-bound strictly below this closes the goal
    pq = None
    for q in range(1, MAX_LOG_DENOM + 1):
        # `E ** p > x_ub ** q` by construction, so `q·log x < p` is certifiable.
        p = math.floor(q * math.log(x_ub) / math.log(LOG_BASE)) + 1
        if p / q < hi:
            pq = (p, q)
            break
    if pq is None:  # no rational log-bound fits this Lehman margin
        return (f"  -- wide: no rational log bound `p/q` (q ≤ {MAX_LOG_DENOM}) fits the Lehman\n"
                "  -- margin here; the block is too narrow. Left as `sorry`.\n  wide := sorry")
    p, q = pq
    return f"""  wide := by
    change {LEHMAN_CONST} + ({LEHMAN_LOG_COEFF} : ℝ) * Real.log ({aN} / (2 * π)) < ({rlN} - {frN}) / 2
    have hπ : ({PI_LOWER} : ℝ) < π := Real.pi_gt_d6
    have hX : (({aN} : ℝ) / (2 * π)) ^ {q} < {LOG_BASE} ^ {p} := by
      rw [div_pow, div_lt_iff₀ (by positivity)]
      calc ({aN} : ℝ) ^ {q} < {LOG_BASE} ^ {p} * {2 * PI_LOWER} ^ {q} := by norm_num
        _ ≤ {LOG_BASE} ^ {p} * (2 * π) ^ {q} := by gcongr; linarith
    have he : ({LOG_BASE} : ℝ) ^ {p} ≤ Real.exp {p} := by
      rw [show Real.exp {p} = Real.exp 1 ^ {p} by rw [← Real.exp_nat_mul]; norm_num]
      gcongr
      nlinarith [Real.exp_one_gt_d9]
    have hlog : ({q} : ℝ) * Real.log ({aN} / (2 * π)) < {p} := by
      rw [show ({q} : ℝ) * Real.log ({aN} / (2 * π))
          = Real.log ((({aN} : ℝ) / (2 * π)) ^ ({q} : ℕ)) by rw [Real.log_pow]; norm_num]
      exact (Real.log_lt_iff_lt_exp (by positivity)).2 (hX.trans_le he)
    nlinarith [hlog]"""


def gen_high(blocks: list[Block]) -> str:
    """Proof of `high : LEHMAN_MIN_HEIGHT_PI·π < head.left.left` — needs only `π < PI_UPPER`.
    `sorry` when the data sits below that height."""
    fll = blocks[0]["left"][1]
    floor_t = LEHMAN_MIN_HEIGHT_PI * float(PI_UPPER)
    if not floor_t < float(fll):
        return (f"  -- high: this data is below {LEHMAN_MIN_HEIGHT_PI}π ≈ {floor_t:.1f} (out of the "
                "Lehman/Turing regime);\n"
                f"  -- regenerate above ~{floor_t:.0f} to discharge. Left as `sorry`.\n  high := sorry")
    return f"""  high := by
    change {LEHMAN_MIN_HEIGHT_PI} * π < ({fll} : ℝ)
    nlinarith [Real.pi_lt_d6]"""


def gen_bundle(blocks: list[Block]) -> str:
    n = len(blocks)
    # wrapped: at ~25 blocks the one-line list passes mathlib's 100-column limit
    names_ = [f"blk{i}" for i in range(1, n + 1)]
    lines, cur = [], ""
    for nm in names_:
        piece = (", " if cur else "") + nm
        if len("  blocks := [") + len(cur) + len(piece) > 96:
            lines.append(cur + ","); cur = nm
        else:
            cur += piece
    lines.append(cur)
    names = "\n    ".join(lines)
    cert_bullets = "\n".join(f"    · exact blk{i}_cert" for i in range(1, n + 1))
    if n == 1:
        seq_proof = "    exact List.isChain_singleton _"
    else:
        # The adjacency relation is `a.right.idx = b.left.idx`; after unfolding the
        # `IsChain` these are literal `Nat` equalities that `simp` reduces and closes
        # outright (unlike the real-number `<` in `gen_zero_certificates`, which needs
        # an explicit `refine … <;> norm_num`).
        seq_proof = (
            "    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]")
    return f"""/-- The certified sequence of good gram blocks: every gram point and contained zero carries a
certificate, the blocks tile consecutively (`seq`), the total span clears the Lehman bound
(`wide`), and the range sits above `168π` (`high`). -/
abbrev certifiedGramBlockSeq : CertifiedGramBlockSeq where
  blocks := [{names}]
  seq := by
{seq_proof}
  cert := by
    intro b hb
    fin_cases hb
{cert_bullets}
  non_empty := by simp
{gen_wide(blocks)}
{gen_high(blocks)}
"""


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit(
            "usage: gen_gram_certificates.py <out_path> <store>\n"
            "  output first, store second — the same order as gen_zero_certificates.py and\n"
            "  gen_count_certificate.py; e.g.\n"
            "  gen_gram_certificates.py ../Zeta/Gram/Certificates.lean out/riemann_siegel/gram"
        )
    out_path = Path(sys.argv[1])
    store = Path(sys.argv[2])
    if not (store / "manifest.json").is_file():
        raise SystemExit(f"{store}: no manifest.json (is this a gram store?)")

    manifest = json.loads((store / "manifest.json").read_text())
    params = manifest.get("params", {})
    dialect = dialect_for(store, manifest)
    prec = params.get("prec", "unrecorded")
    theta = params.get("theta_at_height", "unrecorded")
    gram_pts = parse_gram_points(store / "gram_block.txt")
    blocks = build_blocks(gram_pts, store, manifest, dialect)
    if not blocks:
        raise SystemExit(f"no gram blocks parsed from {store}")

    n_zeros = sum(len(bl["zeros"]) for bl in blocks)
    tactic_import = dialect.tactic_module or "Zeta.Certificate.Named"
    zeros_note = (
        "The zeros' `is_sign_change`/`fst_error`/`snd_error` are discharged the\nsame way."
        if dialect.proves_obligations else
        f"The zeros' `is_sign_change`/`fst_error`/`snd_error`\nremain `sorry`: the certificate engine does not yet cover the\n{dialect.method} approximant.")
    root = Path(__file__).resolve().parents[3]
    try:
        store_rel = store.resolve().relative_to(root)
    except ValueError:
        store_rel = store
    header = f"""/-
Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Bhavik Mehta
-/
/-
AUTO-GENERATED by `python/src/data_gen/gen_gram_certificates.py` from
  {store_rel}
Do not edit by hand: regenerate instead.

{len(blocks)} good gram blocks ({n_zeros} bracketed zeros) packaged as one
`CertifiedGramBlockSeq`, with the zeros bracketed by the {dialect.method} approximant.
Gram-point theta-Stirling parameters are read straight from the store — bracketing a gram
point is a question about `theta`, so they are the same whichever approximant certified the
zeros ({theta}, working precision {prec} bits).

The gram points' `fst_bound`/`snd_bound` are discharged by `gram_bound` (kernel-checked
`Enclosure` ball arithmetic): bracketing a gram point is a question about `theta` alone, so
it is method-independent.
{zeros_note}
The `wide`/`high` sequence bounds are
elementary `π`/`log` inequalities and are discharged when the data is in range; every other
field is automatic.
-/
module

public import Zeta.Gram.Block
public import {dialect.exists_zero_module}
public import {tactic_import}

@[expose] public section

namespace Zeta.Certificates.Gram

open Zeta.Certificates Real Set

"""

    gram_points = gen_gram_points(gram_pts)
    body = "\n".join(gen_block(i, bl, dialect) for i, bl in enumerate(blocks, start=1))
    bundle = gen_bundle(blocks)
    footer = "\nend Zeta.Certificates.Gram\n\nend\n"

    write_module(out_path, header + gram_points + "\n" + body + "\n" + bundle + footer)
    print(f"wrote {out_path} ({len(blocks)} blocks, {n_zeros} zeros)")


if __name__ == "__main__":
    main()
