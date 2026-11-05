/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gram.ZeroCounting
public import Zeta.RiemannVonMangoldt.ZeroCounting

/-!
# Matched zero counts below a gram point

A `CertifiedZeroCount` pins a certified *upper* bound on the number of `ζ`-zeros below a gram
point (a `CertifiedGramBlockSeq`, via Turing's method) against a certified *lower* bound (a
`CertifiedZeroIntervals`, each interval isolating a critical-line zero), forcing every `ζ`-zero
below that height onto the critical line (`Zeta/Zeros/RiemannHypothesisUpTo.lean`).

## Main definitions

- `CertifiedZeroCount`: the matched pair of bounds.

## Main results

- `riemannZeta.zeroes_rect_Ioo_finite`: `ζ` has finitely many zeros of height in `(0, T)`.
- `riemannZeta.le_N_of_certifiedZeroIntervals`: `C.intervals.length ≤ N(C.height)`, the
  certified lower bound on the zero count. Stated here rather than beside
  `CertifiedZeroIntervals` so that the certificate batches never import the counting side.
-/
@[expose] public section


open Zeta.Certificates

/-- The zeros of `ζ` in the box `{Re ∈ ℝ, Im ∈ (0, T)}` form a finite set. -/
theorem riemannZeta.zeroes_rect_Ioo_finite (T : ℝ) :
    (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)).Finite := by
  have hSc : IsCompact ((Set.Icc 0 1 ×ℂ Set.Icc 0 T) : Set ℂ) :=
    isCompact_Icc.reProdIm isCompact_Icc
  apply Set.Finite.subset (riemannZeta.zeroes_on_Compact_finite' hSc)
  rintro z ⟨-, hzim, hz0⟩
  have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 hzim.1.ne'
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨hre.1.le, hre.2.le⟩, ⟨hzim.1.le, hzim.2.le⟩⟩, hz0⟩

/-- **The certified-zero lower bound on `N`.** A certified list of zero intervals witnesses at
least as many `ζ`-zeros below its height as it has intervals:
`C.intervals.length ≤ N(C.height)`. -/
theorem riemannZeta.le_N_of_certifiedZeroIntervals (C : CertifiedZeroIntervals) :
    C.intervals.length ≤ riemannZeta.N C.height := by
  have : Fintype ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) :=
    (zeroes_rect_Ioo_finite C.height).fintype
  have hzero : ∀ k : Fin C.intervals.length,
      ∃ t ∈ Set.Ioo (C.intervals.get k).fst (C.intervals.get k).snd,
        riemannZeta (1 / 2 + Complex.I * t) = 0 :=
    fun k ↦ C.has_zero _ (List.get_mem _ k)
  set t : Fin C.intervals.length → ℝ := fun k ↦ (hzero k).choose with ht
  have htspec : ∀ k, t k ∈ Set.Ioo (C.intervals.get k).fst (C.intervals.get k).snd ∧
      riemannZeta (1 / 2 + Complex.I * (t k : ℂ)) = 0 :=
    fun k ↦ (hzero k).choose_spec
  have hmono : StrictMono t := fun k₁ k₂ hlt ↦
    calc t k₁ < (C.intervals.get k₁).snd := (htspec k₁).1.2
      _ ≤ (C.intervals.get k₂).fst := List.pairwise_iff_get.mp C.pairwise k₁ k₂ hlt
      _ < t k₂ := (htspec k₂).1.1
  have hmem : ∀ k : Fin C.intervals.length,
      (1 / 2 + Complex.I * (t k : ℂ)) ∈ riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height) := by
    refine fun k ↦ ⟨Set.mem_univ _, ?_, (htspec k).2⟩
    rw [show (1 / 2 + Complex.I * (t k : ℂ)).im = t k from by simp]
    exact ⟨(C.fst_nonneg _ (List.get_mem _ k)).trans_lt (htspec k).1.1,
      (htspec k).1.2.trans_le (C.le_height (List.get_mem _ k))⟩
  let g : Fin C.intervals.length → ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) :=
    fun k ↦ ⟨1 / 2 + Complex.I * (t k : ℂ), hmem k⟩
  have hg_inj : Function.Injective g := fun k₁ k₂ hgeq ↦
    hmono.injective (by simpa [g] using congrArg (Complex.im ∘ Subtype.val) hgeq)
  have hcard : C.intervals.length ≤
      Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) := by
    simpa using Fintype.card_le_of_injective g hg_inj
  have hNeq : riemannZeta.N C.height =
      ∑ ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)),
        ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
    rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype]
    exact Finset.sum_congr rfl fun ρ _ ↦ one_mul _
  rw [hNeq]
  calc ((C.intervals.length : ℕ) : ℝ)
      ≤ ((Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height)),
          ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ) := by
        have h := Finset.card_nsmul_le_sum
          (Finset.univ (α := ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 C.height))))
          (fun ρ ↦ ((riemannZeta.order (ρ : ℂ) : ℤ) : ℝ)) 1
          (fun ρ _ ↦ by
            exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ρ)
        rwa [Finset.card_univ, nsmul_eq_mul, mul_one] at h


/-- A matched zero count below a gram point: a certified gram-block sequence (upper bound) and a
certified list of critical-line zero intervals (lower bound) whose counts agree. -/
structure CertifiedZeroCount extends CertifiedGramBlockSeq, CertifiedZeroIntervals where
  /-- Turing's upper bound `minIdx + 1` matches the number of certified zero intervals. -/
  count : toCertifiedGramBlockSeq.minIdx + 1 = intervals.length
  /-- The certified zeros all lie below the gram point at which the count is taken. -/
  below : toCertifiedZeroIntervals.height ≤ gramPoint toCertifiedGramBlockSeq.minIdx
