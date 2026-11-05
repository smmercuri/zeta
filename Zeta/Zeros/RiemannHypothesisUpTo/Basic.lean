/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Zeros.Count
public import Zeta.Zeros.RealZeros
public import Zeta.Zeros.Certificates.Basic

/-!
# The Riemann hypothesis up to a height, from any certificate

The Riemann hypothesis below the head gram point of a `CertifiedZeroCount`, whose matched upper
and lower bounds on the zero count leave no room for an off-line zero. Nothing here depends on the
generated certificate batches: `riemannHypothesisUpTo_of_batchSpec` takes the batches' combined
statement as a hypothesis, which is what lets the batches and the rest of the proof be checked
separately (`comparator/README.md`).

## Main definitions

- `RiemannHypothesisUpTo`: the statement of RH up to a height `T`.

## Main results

- `riemannZeta.le_N_of_zeros`: a nodup list of `ζ`-zeros with ordinates in `(0, T)` has length at
  most `N T`.
- `riemannZeta.ne_zero_of_re_ne_half_upto`: off the critical line, `ζ` has no zero with ordinate
  below the certified gram point.
- `riemannHypothesisUpTo`: RH up to a height, from any `CertifiedZeroCount`.
- `riemannHypothesisUpTo_of_batchSpec`: RH up to a height, from a gram-block sequence and a
  `BatchSpec` whose count and top endpoint match it.
-/
@[expose] public section


open Set
open scoped ComplexConjugate

/-- **A nodup list of `ζ`-zeros with ordinates in `(0, T)` has length at most `N T`.** -/
theorem riemannZeta.le_N_of_zeros {T : ℝ} (Z : List ℂ)
    (hZ : ∀ s ∈ Z, s.im ∈ Ioo 0 T ∧ riemannZeta s = 0)
    (hZ_nodup : Z.Nodup) :
    Z.length ≤ riemannZeta.N T := by
  have hcard : Z.length ≤ Fintype.card ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)) := by
    simpa using Fintype.card_le_of_injective
      (fun k : Fin Z.length ↦ (⟨Z.get k, Set.mem_univ _, (hZ _ (List.get_mem _ k)).1,
        (hZ _ (List.get_mem _ k)).2⟩ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T))))
      fun _ _ h ↦ List.nodup_iff_injective_get.mp hZ_nodup (congrArg Subtype.val h)
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype]
  calc ((Z.length : ℕ) : ℝ)
      ≤ ∑ _ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)), (1 : ℝ) := by
        simpa [Finset.card_univ] using (Nat.cast_le (α := ℝ)).2 hcard
    _ ≤ _ := Finset.sum_le_sum fun ρ _ ↦ by
        rw [one_mul]
        exact_mod_cast Kadiri.riemannZeta_one_le_order_positiveHeightZero ρ

/-- **No off-line zero below the certified gram point.** -/
theorem riemannZeta.ne_zero_of_re_ne_half_upto {s : ℂ} (Z : CertifiedZeroCount)
    (hs : s.im ∈ Ioo 0 (gramPoint Z.minIdx)) (hσ : s.re ≠ 1 / 2) :
    riemannZeta s ≠ 0 := by
  let n := Z.intervals.length
  have hN : riemannZeta.N (gramPoint Z.minIdx) = n := by
    apply le_antisymm
    · simp only [← Z.count, Nat.cast_add, Nat.cast_one, n]
      exact riemannZeta.N_le_of_certifiedGramBlockSeq Z.toCertifiedGramBlockSeq
    · simp only [n]
      grw [← riemannZeta.N_mono Z.below]
      exact riemannZeta.le_N_of_certifiedZeroIntervals Z.toCertifiedZeroIntervals
  intro hs_zero
  have : s ∉ Z.zeros := by grind [Z.zeros_re]
  let Z' := s::Z.zeros
  have := riemannZeta.le_N_of_zeros (T := gramPoint Z.minIdx) Z' (by
    simp only [List.mem_cons, forall_eq_or_imp, Z']
    refine ⟨⟨hs, hs_zero⟩, fun a ha ↦ ?_⟩
    refine ⟨Ioo_subset_Ioo le_rfl Z.below (Z.zeros_im ha), ?_⟩
    exact (Z.zeros_spec a ha).2) (by simp [Z', this, Z.zeros_nodup])
  simp [Z', Z.zeros_length] at this
  grind

/-- The statement that the Riemann hypothesis holds within the domain
`{ 1 / 2 + I * t ∣ |s.im| < T }`. -/
def RiemannHypothesisUpTo (T : ℝ) : Prop :=
  ∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < T → s.re = 1/2

/-- **The Riemann hypothesis up to the certified gram point.** -/
theorem riemannHypothesisUpTo (Z : CertifiedZeroCount) :
    RiemannHypothesisUpTo (gramPoint Z.minIdx) := by
  intro s h_zero h_non_trivial hs_one hs_im
  by_contra! hs_re
  rcases lt_trichotomy s.im 0 with (h_neg | h_eq | h_pos)
  · rw [abs_of_neg h_neg] at hs_im
    refine riemannZeta.ne_zero_of_re_ne_half_upto Z (s := conj s)
      (by simpa using ⟨h_neg, hs_im⟩) (by simpa using hs_re) ?_
    rw [riemannZeta_conj, h_zero, map_zero]
  · have := riemannZeta_ofReal_ne_zero (x := s.re)
    rw [← s.conj_eq_iff_re.1 <| s.conj_eq_iff_im.2 h_eq] at h_non_trivial h_zero
    aesop
  · rw [abs_of_nonneg h_pos.le] at hs_im
    exact riemannZeta.ne_zero_of_re_ne_half_upto Z ⟨h_pos, hs_im⟩ hs_re h_zero

open Zeta.Certificates in
/-- **The Riemann hypothesis from a batch statement.** A certified gram-block sequence and a
`BatchSpec` whose interval count is the sequence's `minIdx + 1` and whose last endpoint lies below
its head gram point give RH up to that gram point. -/
theorem riemannHypothesisUpTo_of_batchSpec {n an ad bn bd : ℕ} (G : CertifiedGramBlockSeq)
    (h : BatchSpec n an ad bn bd) (hcount : G.minIdx + 1 = n)
    (hbelow : Enclosure.sfrac false bn bd ≤ gramPoint G.minIdx) :
    RiemannHypothesisUpTo (gramPoint G.minIdx) :=
  riemannHypothesisUpTo
    { toCertifiedGramBlockSeq := G
      toCertifiedZeroIntervals := h.bundle
      count := by rw [h.bundle_length]; exact hcount
      below := h.bundle.height_le_of_getLast?_snd h.bundle_getLast? hbelow }

end
