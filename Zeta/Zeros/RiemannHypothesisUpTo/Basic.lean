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
- `SimpleZerosUpTo`: the statement that every zero with ordinate in `(0, T)` is simple.

## Main results

- `riemannZeta.le_N_of_zeros`: a nodup list of `ζ`-zeros with ordinates in `(0, T)` has length at
  most `N T`.
- `riemannZeta.ne_zero_of_re_ne_half_upto`: off the critical line, `ζ` has no zero with ordinate
  below the certified gram point.
- `riemannHypothesisUpTo`: RH up to a height, from any `CertifiedZeroCount`.
- `simpleZerosUpTo`: every zero up to that height is simple, from the same certificate.
- `riemannHypothesisUpTo_of_batchSpec`: RH up to a height, from a gram-block sequence and a
  `BatchSpec` whose count and top endpoint match it.
-/
@[expose] public section


open Set
open scoped ComplexConjugate

/-- A nodup list of `ζ`-zeros with ordinates in `(0, T)` has length at most `N T`. -/
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

/-- The certificate pins `N` at its head gram point: Turing's upper bound `minIdx + 1` and the
lower bound from the certified intervals agree. -/
theorem riemannZeta.N_gramPoint_eq (Z : CertifiedZeroCount) :
    riemannZeta.N (gramPoint Z.minIdx) = Z.intervals.length := by
  apply le_antisymm
  · simp only [← Z.count, Nat.cast_add, Nat.cast_one]
    exact riemannZeta.N_le_of_certifiedGramBlockSeq Z.toCertifiedGramBlockSeq
  · grw [← riemannZeta.N_mono Z.below]
    exact riemannZeta.le_N_of_certifiedZeroIntervals Z.toCertifiedZeroIntervals

/-- Every zero of `ζ` with ordinate in `(0, gramPoint Z.minIdx)` has real part `1/2`. -/
theorem riemannZeta.ne_zero_of_re_ne_half_upto {s : ℂ} (Z : CertifiedZeroCount)
    (hs : s.im ∈ Ioo 0 (gramPoint Z.minIdx)) (hσ : s.re ≠ 1 / 2) :
    riemannZeta s ≠ 0 := by
  let n := Z.intervals.length
  have hN : riemannZeta.N (gramPoint Z.minIdx) = n := riemannZeta.N_gramPoint_eq Z
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

/-- Every zero below the certified gram point is simple. `N` counts zeros with multiplicity
and the certificate pins it to the number of intervals, each holding a distinct zero, so a zero of
order at least two would push `N` past that number. -/
theorem riemannZeta.order_eq_one_upto {s : ℂ} (Z : CertifiedZeroCount)
    (hs : s.im ∈ Ioo 0 (gramPoint Z.minIdx)) (hs_zero : riemannZeta s = 0) :
    riemannZeta.order s = 1 := by
  set S := (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 (gramPoint Z.minIdx))).toFinset
  have hmem : ∀ z, z ∈ S ↔ z.im ∈ Ioo 0 (gramPoint Z.minIdx) ∧ riemannZeta z = 0 := fun z ↦ by
    rw [Set.mem_toFinset]
    simp [riemannZeta.zeroes_rect, riemannZeta.zeroes]
  have hpos : ∀ z ∈ S, (1 : ℤ) ≤ riemannZeta.order z := fun z hz ↦
    Kadiri.riemannZeta_one_le_order_positiveHeightZero ⟨z, Set.mem_toFinset.1 hz⟩
  have hsS : s ∈ S := (hmem s).2 ⟨hs, hs_zero⟩
  have hcard : (Z.intervals.length : ℝ) ≤ S.card := by
    rw [← Z.zeros_length, ← List.toFinset_card_of_nodup Z.zeros_nodup]
    refine Nat.cast_le.2 (Finset.card_le_card fun z hz ↦ (hmem z).2 ?_)
    obtain ⟨him, hz0⟩ := Z.zeros_spec z (List.mem_toFinset.1 hz)
    exact ⟨Ioo_subset_Ioo le_rfl Z.below him, hz0⟩
  have hsum : ∑ ρ ∈ S, (riemannZeta.order ρ : ℝ) =
      ∑ ρ ∈ S, ((riemannZeta.order ρ : ℝ) - 1) + S.card := by
    simp [Finset.sum_sub_distrib]
  have hs1 : (riemannZeta.order s : ℝ) - 1 ≤ ∑ ρ ∈ S, ((riemannZeta.order ρ : ℝ) - 1) :=
    Finset.single_le_sum (f := fun ρ ↦ (riemannZeta.order ρ : ℝ) - 1)
      (fun ρ hρ ↦ sub_nonneg.2 (by exact_mod_cast hpos ρ hρ)) hsS
  have hN := riemannZeta.N_gramPoint_eq Z
  rw [riemannZeta.N_eq_sum] at hN
  have hle : (riemannZeta.order s : ℝ) ≤ 1 := by linarith
  exact le_antisymm (by exact_mod_cast hle) (hpos s hsS)

/-- Every zero below the certified gram point is simple, as Mathlib's meromorphic order. -/
theorem riemannZeta.meromorphicOrderAt_eq_one_upto {s : ℂ} (Z : CertifiedZeroCount)
    (hs : s.im ∈ Ioo 0 (gramPoint Z.minIdx)) (hs_zero : riemannZeta s = 0) :
    meromorphicOrderAt riemannZeta s = 1 := by
  have h := riemannZeta.order_eq_one_upto Z hs hs_zero
  rw [riemannZeta.order] at h
  cases hm : meromorphicOrderAt riemannZeta s with
  | top => simp [hm] at h
  | coe n => simp_all

/-- The statement that the Riemann hypothesis holds within the domain
`{ 1 / 2 + I * t ∣ |s.im| < T }`. -/
def RiemannHypothesisUpTo (T : ℝ) : Prop :=
  ∀ s, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| < T → s.re = 1/2

/-- The statement that every zero of `riemannZeta` with ordinate in `(0, T)` is simple. -/
def SimpleZerosUpTo (T : ℝ) : Prop :=
  ∀ s, riemannZeta s = 0 → s.im ∈ Ioo 0 T → meromorphicOrderAt riemannZeta s = 1

/-- Simple zeros up to a height imply them up to any smaller height. -/
theorem SimpleZerosUpTo.mono {S T : ℝ} (hST : S ≤ T) (h : SimpleZerosUpTo T) :
    SimpleZerosUpTo S :=
  fun s h₀ hs ↦ h s h₀ ⟨hs.1, hs.2.trans_le hST⟩

/-- Every zero up to the certified gram point is simple. -/
theorem simpleZerosUpTo (Z : CertifiedZeroCount) : SimpleZerosUpTo (gramPoint Z.minIdx) :=
  fun _ h₀ hs ↦ riemannZeta.meromorphicOrderAt_eq_one_upto Z hs h₀

/-- The Riemann hypothesis up to a height implies it up to any smaller height. -/
theorem RiemannHypothesisUpTo.mono {S T : ℝ} (hST : S ≤ T) (h : RiemannHypothesisUpTo T) :
    RiemannHypothesisUpTo S :=
  fun s h₀ hn h₁ hs => h s h₀ hn h₁ (hs.trans_le hST)

/-- The Riemann hypothesis up to `T`, stated for zeros in the critical strip with `|ρ.im| ≤ H`, for
any `H < T`. -/
theorem RiemannHypothesisUpTo.closed_strip {H T : ℝ} (hH : H < T) (h : RiemannHypothesisUpTo T) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2 := by
  intro ρ hρ h0 h1 him
  refine h ρ hρ ?_ ?_ (him.trans_lt hH)
  · rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [hre] at h0
    linarith
  · rintro rfl
    simp at h1

/-- The Riemann hypothesis up to the certified gram point. -/
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
/-- The Riemann hypothesis from a batch statement: a certified gram-block sequence and a
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
