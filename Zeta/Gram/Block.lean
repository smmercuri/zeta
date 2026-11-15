/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.Interval

/-!
# Certified gram blocks

A `GramPoint` is an interval bracketing the `n`-th gram point (the solution of `θ(t) = n·π`),
together with the Stirling data used to estimate `θ` at its endpoints; its `Certificate` records
that the two computed values straddle `n·π` by more than their error bounds. A `GramBlock` pairs
two consecutive certified gram points with a list of zero intervals lying between them, and a
`CertifiedGramBlockSeq` chains such blocks; this is the input to Turing's method.

## Main definitions

- `GramPoint`, `GramPoint.fstVal`, `GramPoint.sndVal`, `GramPoint.Certificate`: a bracketed
  gram point, its two computed `θ`-values, and its certificate.
- `GramBlock`, `GramBlock.Certificate`: two consecutive gram points enclosing certified zeros.
- `CertifiedGramBlockSeq`, `CertifiedGramBlockSeq.minIdx`: a chain of certified gram blocks and
  the gram index at its head.

## Main results

- `GramPoint.certificate_theta_left_lt`, `GramPoint.certificate_theta_right_gt`: a certified gram
  point brackets `θ = n·π`.
- `CertifiedGramBlockSeq.getElem_left_idx`: the `j`-th block of a chain has left index
  `minIdx + j`.
-/
@[expose] public section


namespace Zeta.Certificates

open Real Set

/-- An interval bracketing the `n`-th gram point (`θ(t) = n·π`), with the Stirling orders and
shifts used to estimate `θ` at its endpoints. -/
structure GramPoint extends NonemptyInterval ℝ where
  /-- The gram index `n`. -/
  idx : ℕ
  /-- The Stirling shift used to estimate `θ` at the left endpoint. -/
  fstCutoff : ℕ
  /-- The number of Bernoulli terms used to estimate `θ` at the left endpoint. -/
  fstBernoulli : ℕ
  /-- The Stirling shift used to estimate `θ` at the right endpoint. -/
  sndCutoff : ℕ
  /-- The number of Bernoulli terms used to estimate `θ` at the right endpoint. -/
  sndBernoulli : ℕ

/-- The approximate value of `θ` at the left endpoint. -/
noncomputable abbrev GramPoint.fstVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.fstBernoulli G.fstCutoff G.fst

/-- The approximate value of `θ` at the right endpoint. -/
noncomputable abbrev GramPoint.sndVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.sndBernoulli G.sndCutoff G.snd

/-- A certificate that the interval `G` brackets the gram point of index `G.idx`. -/
structure GramPoint.Certificate (G : GramPoint) where
  /-- Required for the Riemann–Siegel theta error bound at the left endpoint. -/
  fst_nonneg : 0 ≤ G.fst
  /-- Required for the Riemann–Siegel theta error bound at the right endpoint. -/
  snd_nonneg : 0 ≤ G.snd
  /-- Required for the log-Γ Stirling remainder bound at the left endpoint. -/
  fstBernoulli_pos : 0 < G.fstBernoulli
  /-- Required for the log-Γ Stirling remainder bound at the right endpoint. -/
  sndBernoulli_pos : 0 < G.sndBernoulli
  /-- The computed left value falls short of `G.idx · π` by more than its error bound. -/
  fst_bound : G.idx * π - G.fstVal >
    riemannSiegelThetaStirlingErrorBound' G.fstBernoulli G.fstCutoff G.fst
  /-- The computed right value exceeds `G.idx · π` by more than its error bound. -/
  snd_bound : G.sndVal - G.idx * π >
    riemannSiegelThetaStirlingErrorBound' G.sndBernoulli G.sndCutoff G.snd

/-- Two consecutive gram points together with the zero intervals lying between them. -/
structure GramBlock where
  /-- The gram point of index `n`. -/
  left : GramPoint
  /-- The gram point of index `n + 1`. -/
  right : GramPoint
  /-- The zero intervals carried by the block. -/
  zeros : List (NonemptyInterval ℝ)
  /-- The two gram indices are consecutive. -/
  seq : left.idx + 1 = right.idx
  /-- The left bracket ends at or before the right one begins. Each bracket is separately
  non-empty by `GramPoint.fst_le_snd`. -/
  separated : left.snd ≤ right.fst

/-- A certificate that the gram pair `G` brackets the gram points `n·π` and `(n+1)·π` and
encloses a certified zero of Hardy's `Z` between them. -/
structure GramBlock.Certificate (G : GramBlock) where
  /-- The left gram point is certified. -/
  left_certificate : G.left.Certificate
  /-- The right gram point is certified. -/
  right_certificate : G.right.Certificate
  /-- Every interval carried by the block brackets a `ζ`-zero. The block records the fact rather
  than a certificate, so either approximation method may have certified it. -/
  has_zero : ∀ z ∈ G.zeros, ∃ t ∈ Set.Ioo z.fst z.snd, riemannZeta (1 / 2 + Complex.I * t) = 0
  /-- Some zero interval lies between the two gram brackets. -/
  contains_zero : ∃ z ∈ G.zeros, z.fst ∈ Icc G.left.snd G.right.fst ∧
    z.snd ∈ Icc G.left.snd G.right.fst

/-- A chain of certified gram blocks with consecutive indices, spanning a range wide enough
(`wide`) and high enough (`high`) for Turing's method. -/
structure CertifiedGramBlockSeq where
  /-- The blocks, in increasing order. -/
  blocks : List GramBlock
  /-- Consecutive blocks share a gram index. -/
  seq : blocks.IsChain fun a b ↦ a.right.idx = b.left.idx
  /-- Every block is certified. -/
  cert : ∀ b ∈ blocks, b.Certificate
  /-- The chain is non-empty. -/
  non_empty : blocks ≠ []
  /-- The span of the chain exceeds the Lehman bound on `|∫S|`. -/
  wide : (5 + (0.128 : ℝ) * ((blocks.getLast non_empty).right.snd / (2 * π)).log) <
    ((blocks.getLast non_empty).right.fst - (blocks.head non_empty).left.snd) / 2
  /-- The chain sits above `168π`, as the Lehman bound requires. -/
  high : 168 * π < (blocks.head non_empty).left.fst

/-- The gram index at the head of a certified chain. -/
abbrev CertifiedGramBlockSeq.minIdx (C : CertifiedGramBlockSeq) : ℕ :=
  (C.blocks.head C.non_empty).left.idx

/-- At the left endpoint of a certified gram point, `θ` lies strictly below `G.idx · π`. -/
theorem GramPoint.certificate_theta_left_lt {G : GramPoint} (h : G.Certificate) :
    riemannSiegelTheta G.fst < (G.idx : ℝ) * π := by
  have hb := abs_le.1 <| abs_riemannSiegelTheta_sub_stirling_shift_le' (N := G.fstCutoff)
    h.fstBernoulli_pos h.fst_nonneg
  linarith [hb.2, h.fst_bound]

/-- At the right endpoint of a certified gram point, `θ` lies strictly above `G.idx · π`. -/
theorem GramPoint.certificate_theta_right_gt {G : GramPoint} (h : G.Certificate) :
    (G.idx : ℝ) * π < riemannSiegelTheta G.snd := by
  have hb := abs_le.1 <| abs_riemannSiegelTheta_sub_stirling_shift_le' (N := G.sndCutoff)
    h.sndBernoulli_pos h.snd_nonneg
  linarith [hb.1, h.snd_bound]

/-- In a certified gram block sequence, the left index of the `j`-th block is `minIdx + j`. -/
theorem CertifiedGramBlockSeq.getElem_left_idx (S : CertifiedGramBlockSeq) (j : ℕ) :
    ∀ (hj : j < S.blocks.length),
      (S.blocks[j]).left.idx = (S.blocks.head S.non_empty).left.idx + j := by
  induction j with
  | zero => intro hj; rw [List.head_eq_getElem_zero S.non_empty, Nat.add_zero]
  | succ i ih =>
    intro hj
    have hi : i < S.blocks.length := Nat.lt_of_succ_lt hj
    linarith [List.isChain_iff_getElem.1 S.seq i (by lia), (S.blocks[i]'hi).seq, ih hi]

end Zeta.Certificates
