/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardConcrete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Set.Card.Arithmetic

/-!
# Minimum modulus of the `ξ`-canonical product

The minimum-modulus lower bound `log ‖P(s)‖ ≥ -C' R^{3/2}` on a good circle, for
`P = riemannXiCanonicalProduct riemannXiZeros`, together with its supporting elementary bounds,
zero counts, radius selection and Hölder sums (`cartan_minimum_modulus.tex`, `cha:cartan`).

## Main results

* `neg_le_log_norm_weierstrassE1` (`lem:cm_elem_lower`): `-4 ‖w‖² ≤ log ‖E₁(w)‖`.
* `Real.log_add_one_sq_le` (`lem:cm_logsq_le`): `(log R + 1)² ≤ 16 R^{1/2}`.
* `exists_card_riemannXiZeros_le` (`lem:cm_card`), with `ncard_setOf_norm_riemannXiZeros_le_eq`.
* `exists_mem_Icc_forall_le_dist` (`lem:cm_radial_select`): the radius pigeonhole.
* `summable_inv_norm_rpow_riemannXiZeros` (`lem:cm_summable_rpow`),
  `exists_sum_inv_norm_riemannXiZeros_le` (`lem:cm_sum_inv`),
  `exists_sum_inv_norm_sq_riemannXiZeros_tail_le` (`lem:cm_sum_inv_sq_tail`).
* `exists_tsum_far_log_norm_weierstrassE1_ge` (`lem:cm_far_lower`),
  `exists_finset_near_log_norm_weierstrassE1_ge` (`lem:cm_near_lower`).
* `exists_circle_log_norm_riemannXiCanonicalProduct_ge` (`thm:cm_minmod` = `lem:hf_minmod`).
-/
@[expose] public section


open Complex Filter Topology MeasureTheory


/-! ### Elementary lower bounds for the factor and the logarithm -/

/-- Quadratic lower bound on the elementary factor (`lem:cm_elem_lower`). For `‖w‖ ≤ 1/2`,
`-4 ‖w‖² ≤ log ‖E₁(w)‖`. -/
theorem neg_le_log_norm_weierstrassE1 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    -4 * ‖w‖ ^ 2 ≤ Real.log ‖weierstrassE1 w‖ := by
  -- `x := 2‖w‖² ∈ [0, 1/2]`, and `‖E₁ w‖ ≥ 1 - x ≥ 1/2`.
  set x : ℝ := 2 * ‖w‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 1 / 2 := by rw [hx]; nlinarith [norm_nonneg w]
  have hpos : 0 < 1 - x := by linarith
  have hge : 1 - x ≤ ‖weierstrassE1 w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (weierstrassE1 w)
    rw [norm_one, norm_sub_rev] at h
    linarith [norm_weierstrassE1_sub_one_le hw]
  -- `log ‖E₁ w‖ ≥ log (1 - x) ≥ -2x = -4‖w‖²`, the last step from `log y⁻¹ ≤ y⁻¹ - 1`.
  have hlog : -(2 * x) ≤ Real.log (1 - x) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - x)⁻¹ by positivity)
    rw [Real.log_inv] at h
    nlinarith [mul_inv_cancel₀ hpos.ne', inv_nonneg.mpr hpos.le,
      mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]
  calc -4 * ‖w‖ ^ 2 = -(2 * x) := by rw [hx]; ring
    _ ≤ Real.log (1 - x) := hlog
    _ ≤ Real.log ‖weierstrassE1 w‖ := Real.log_le_log hpos hge

/-- A square-root domination of the squared logarithm (`lem:cm_logsq_le`). For `R ≥ 1`,
`(log R + 1)² ≤ 16 R^{1/2}`. -/
theorem Real.log_add_one_sq_le {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R + 1) ^ 2 ≤ 16 * R ^ (1 / 2 : ℝ) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hnn : 0 ≤ Real.log R + 1 := by linarith [Real.log_nonneg hR]
  -- `log R = 4 log (R^{1/4}) ≤ 4 (R^{1/4} - 1)`, so `log R + 1 ≤ 4 R^{1/4}`.
  have hle : Real.log R + 1 ≤ 4 * R ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hR0 (1 / 4 : ℝ))
    rw [Real.log_rpow hR0] at h; linarith
  calc (Real.log R + 1) ^ 2 ≤ (4 * R ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
    _ = 16 * R ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hR0.le]; norm_num

/-! ### Cardinality of the truncated zero set -/

/-- The fibre `{i | ρ_i = z}` of the zero enumeration is finite. -/
theorem finite_setOf_riemannXiZeros_eq (z : ℂ) :
    {i : RiemannXiZerosIndex | riemannXiZeros i = z}.Finite := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i : RiemannXiZerosIndex | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i; simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset, ← Set.finite_coe_iff]
    exact Finite.of_equiv _ (Equiv.sigmaSubtype
      (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)).symm
  · have hempty : {i : RiemannXiZerosIndex | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h; exact hz (h ▸ i.1.2)
    rw [hempty]; exact Set.finite_empty

/-- The set of zeros (with multiplicity) `z ∈ supp(D)` in the closed ball of radius `t`. -/
private def zerosInBall (t : ℝ) : Set ℂ :=
  {z | z ∈ (MeromorphicOn.divisor riemannXi ⊤).support ∧ ‖z‖ ≤ t}

private theorem finite_zerosInBall (t : ℝ) : (zerosInBall t).Finite := by
  refine ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t)).finiteSupport
    (isCompact_closedBall 0 t)).subset fun z hz ↦ ?_
  obtain ⟨hzsupp, hzt⟩ := hz
  have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzt
  rw [Function.mem_support, divisor_riemannXi_closedBall_eq t hzb]
  rwa [Function.mem_support] at hzsupp

private theorem setOf_norm_le_eq_biUnion (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}
      = ⋃ z ∈ zerosInBall t, {i : RiemannXiZerosIndex | riemannXiZeros i = z} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  exact ⟨fun hi ↦ ⟨riemannXiZeros i, ⟨i.1.2, hi⟩, rfl⟩, fun ⟨_, ⟨_, hzt⟩, hz⟩ ↦ hz ▸ hzt⟩

/-- The truncated zero index set `{i | ‖ρ_i‖ ≤ t}` is finite. -/
theorem finite_setOf_norm_riemannXiZeros_le (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.Finite := by
  rw [setOf_norm_le_eq_biUnion]
  exact (finite_zerosInBall t).biUnion fun z _ ↦ finite_setOf_riemannXiZeros_eq z

/-- The truncated index count equals the zero-counting function. -/
theorem ncard_setOf_norm_riemannXiZeros_le_eq (t : ℝ) :
    (({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ)) = riemannXiZeroCount t := by
  have hZfin := finite_zerosInBall t
  set Zf := hZfin.toFinset
  -- `ncard I(t) = ∑ z ∈ Zf, (D z).toNat`
  have hncard : {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard
      = ∑ z ∈ Zf, (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
    rw [setOf_norm_le_eq_biUnion,
      Set.Finite.ncard_biUnion hZfin (fun z _ ↦ finite_setOf_riemannXiZeros_eq z) ?_]
    · rw [← hZfin.coe_toFinset, finsum_mem_coe_finset]
      exact Finset.sum_congr rfl fun z _ ↦ ncard_setOf_riemannXiZeros_eq z
    · intro z₁ _ z₂ _ hne
      refine Set.disjoint_left.mpr fun i hi1 hi2 ↦ hne ?_
      simp only [Set.mem_ofPred_eq] at hi1 hi2
      rw [← hi1, ← hi2]
  -- `riemannXiZeroCount t = ∑ z ∈ Zf, (D z).toNat`
  have hcount : riemannXiZeroCount t
      = ∑ z ∈ Zf, ((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℝ) := by
    have hdef : riemannXiZeroCount t
        = ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z : ℤ) : ℝ) := rfl
    rw [hdef, finsum_eq_finsetSum_of_support_subset _ (s := Zf) ?subset]
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using (hZfin.mem_toFinset.mp hz).2
      rw [divisor_riemannXi_closedBall_eq t hzb]
      exact (divisor_riemannXi_toNat_cast z).symm
    case subset =>
      intro z hz
      have hzint : MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z ≠ 0 :=
        Int.cast_ne_zero.mp (Function.mem_support.mp hz)
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        by_contra hb
        exact hzint (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb)
      rw [Finset.mem_coe, hZfin.mem_toFinset]
      refine ⟨Function.mem_support.mpr ?_, by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzb⟩
      rw [← divisor_riemannXi_closedBall_eq t hzb]; exact hzint
  rw [hncard, hcount, Nat.cast_sum]

/-- Cardinality of the truncated zero set (`lem:cm_card`). There is `C_n > 0` with
`#{i | ‖ρ_i‖ ≤ t} ≤ C_n t log t` for all `t ≥ 2`. -/
theorem exists_card_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      ({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ) ≤ C * (t * Real.log t) := by
  obtain ⟨C, hC, hbound⟩ := riemannXiZeroCount_le
  exact ⟨C, hC, fun t ht ↦ by rw [ncard_setOf_norm_riemannXiZeros_le_eq t]; exact hbound t ht⟩

/-! ### One-dimensional radius selection -/

/-- Avoiding finitely many points on an interval (`lem:cm_radial_select`). If `S` is a finite
set of reals, `a ≤ b`, `δ > 0` and `2 δ (#S) < b - a`, then there is `r ∈ [a, b]` with
`δ ≤ |r - t|` for every `t ∈ S`. -/
theorem exists_mem_Icc_forall_le_dist {S : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hcard : 2 * δ * S.card < b - a) :
    ∃ r ∈ Set.Icc a b, ∀ t ∈ S, δ ≤ |r - t| := by
  classical
  set B : Set ℝ := ⋃ t ∈ S, Set.Ioo (t - δ) (t + δ) with hB
  -- `volume B ≤ 2 δ (#S) < b - a = volume (Icc a b)`.
  have hlt : volume B < volume (Set.Icc a b) := by
    have hvolB : volume B ≤ ENNReal.ofReal (2 * δ * S.card) := by
      refine (measure_biUnion_finset_le S _).trans ?_
      rw [show ENNReal.ofReal (2 * δ * S.card) = ∑ _t ∈ S, ENNReal.ofReal (2 * δ) from by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring]
      exact Finset.sum_le_sum fun t _ ↦ le_of_eq (by rw [Real.volume_Ioo]; congr 1; ring)
    rw [Real.volume_Icc]
    exact hvolB.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hcard)
  -- the complement in `[a, b]` is nonempty.
  obtain ⟨r, hrIcc, hrB⟩ : (Set.Icc a b \ B).Nonempty :=
    nonempty_of_measure_ne_zero (μ := volume) fun hzero ↦ absurd
      ((measure_mono (Set.subset_sdiff_union (Set.Icc a b) B)).trans
        ((measure_union_le _ _).trans_eq (by rw [hzero, zero_add]))) (not_le.mpr hlt)
  refine ⟨r, hrIcc, fun t ht ↦ ?_⟩
  -- `r ∉ Ioo (t - δ, t + δ)`, hence `|r - t| ≥ δ`.
  have hrt : r ∉ Set.Ioo (t - δ) (t + δ) := fun h ↦ hrB (by rw [hB]; exact Set.mem_biUnion ht h)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hrt
  rcases hrt with h | h
  · exact le_abs.mpr (.inr (by linarith))
  · exact le_abs.mpr (.inl (by linarith))

/-! ### Hölder bounds on inverse zero moduli -/

/-- Hölder bookkeeping: `a⁻¹ ^ p * a ^ q = a ^ (q - p)` for `a > 0`. -/
private lemma inv_rpow_mul_rpow {a : ℝ} (ha : 0 < a) (p q : ℝ) :
    a⁻¹ ^ p * a ^ q = a ^ (q - p) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring

/-- Summability of the `p`-power of inverse moduli (`lem:cm_summable_rpow`). For `p > 1` the
family `i ↦ ‖ρ_i⁻¹‖ ^ p` is summable. -/
theorem summable_inv_norm_rpow_riemannXiZeros {p : ℝ} (hp : 1 < p) :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ p) := by
  rw [summable_sigma_of_nonneg fun _ ↦ by positivity]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  have hbase := summable_riemannXiDivisor_norm_rpow hp
  refine (hbase.subtype (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  have hz0 : z.1 ≠ 0 := by
    intro h
    have hmem := Function.mem_support.mp z.2
    rw [h, divisor_riemannXi_apply_zero] at hmem
    exact hmem rfl
  rw [tsum_fintype]
  simp only [riemannXiZeros, Function.comp_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show ‖z.1⁻¹‖ ^ p = ‖z.1‖ ^ (-p) from by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)],
    divisor_riemannXi_toNat_cast z.1]

/-- The Hölder majorant `S = ∑' ‖ρ_i⁻¹‖^{3/2}`. -/
private noncomputable def holderSum : ℝ :=
  ∑' i : RiemannXiZerosIndex, ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)

private theorem summable_inv_norm_rpow_three_halves :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :=
  summable_inv_norm_rpow_riemannXiZeros (by norm_num)

private theorem holderSum_nonneg : 0 ≤ holderSum := tsum_nonneg fun _ ↦ by positivity

/-- If on a set `s` of zeros the summand `f` is pointwise
`≤ e · ‖ρ⁻¹‖^{3/2}`, then `∑_{i ∈ s} f i ≤ (S + 1) · e`. -/
private theorem tsum_subtype_le_of_le_mul {s : Set RiemannXiZerosIndex}
    {f : RiemannXiZerosIndex → ℝ} (hfs : Summable fun i : s ↦ f (i : RiemannXiZerosIndex))
    {e : ℝ} (he : 0 ≤ e)
    (hf : ∀ i ∈ s, f i ≤ e * ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :
    ∑' i : s, f (i : RiemannXiZerosIndex) ≤ (holderSum + 1) * e :=
  calc ∑' i : s, f (i : RiemannXiZerosIndex)
      ≤ ∑' i : s, e * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) :=
        Summable.tsum_le_tsum (fun i ↦ hf i i.2) hfs
          ((summable_inv_norm_rpow_three_halves.subtype s).mul_left _)
    _ = e * ∑' i : s, ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ e * holderSum :=
        mul_le_mul_of_nonneg_left
          (summable_inv_norm_rpow_three_halves.tsum_subtype_le _ s fun _ ↦ by positivity) he
    _ ≤ (holderSum + 1) * e := by nlinarith [holderSum_nonneg]

/-- Head sum of inverse moduli (`lem:cm_sum_inv`). There is `C₁ > 0` such that for every
`t ≥ 0`, `∑_{‖ρ_i‖ ≤ t} ‖ρ_i⁻¹‖ ≤ C₁ t^{1/2}`. -/
theorem exists_sum_inv_norm_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le t).toFinset, ‖(riemannXiZeros i)⁻¹‖
        ≤ C * t ^ (1 / 2 : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  rw [← Finset.tsum_subtype (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)]
  refine tsum_subtype_le_of_le_mul (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)
    (e := t ^ (1 / 2 : ℝ)) Summable.of_finite (Real.rpow_nonneg ht _) fun i hi ↦ ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  calc a⁻¹
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (1 / 2 - 3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hi (by norm_num)) (by positivity)
    _ = t ^ (1 / 2 : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring

/-- Tail sum of inverse squared moduli (`lem:cm_sum_inv_sq_tail`). There is `C₂ > 0` such that
for every `t > 0`, `∑_{‖ρ_i‖ > t} ‖ρ_i⁻¹‖² ≤ C₂ t^{-1/2}`. -/
theorem exists_sum_inv_norm_sq_riemannXiZeros_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      ∑' i : {i : RiemannXiZerosIndex // t < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 ≤ C * t ^ (-(1 / 2) : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  refine tsum_subtype_le_of_le_mul (s := {i | t < ‖riemannXiZeros i‖})
    (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) (e := t ^ (-(1 / 2) : ℝ))
    (summable_inv_norm_sq_riemannXiZeros.subtype _) (Real.rpow_nonneg ht.le _) fun i hi ↦ ?_
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := lt_trans ht hi
  calc a⁻¹ ^ 2
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (-(1 / 2) - 3 / 2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) by norm_num,
          Real.rpow_mul ha.le, Real.rpow_natCast, Real.rpow_neg_one, ← inv_pow]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ht hi.le (by norm_num)) (by positivity)
    _ = t ^ (-(1 / 2) : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring

/-! ### Lower bounds on the near and far parts -/

private lemma self_mul_rpow_half {R : ℝ} (hR : 0 < R) :
    R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]

private lemma far_rpow_id {R : ℝ} (hR : 0 < R) :
    16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ) = 8 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; norm_num
  have hRid : R ^ 2 * R ^ (-(1 / 2) : ℝ) = R ^ (3 / 2 : ℝ) := by
    have h2 : R ^ 2 = R ^ (2 : ℝ) := by rw [← Real.rpow_natCast R 2]; norm_num
    rw [h2, ← Real.rpow_add hR, show (2 : ℝ) + -(1 / 2) = 3 / 2 by norm_num]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 16 * R ^ 2 * (1 / 2 * R ^ (-(1 / 2) : ℝ)) = 8 * (R ^ 2 * R ^ (-(1 / 2) : ℝ)) by ring, hRid]

private lemma near_rpow_id {R : ℝ} (hR : 0 < R) :
    2 * R * (4 * R) ^ (1 / 2 : ℝ) = 4 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 2 * R * (2 * R ^ (1 / 2 : ℝ)) = 4 * (R * R ^ (1 / 2 : ℝ)) by ring, self_mul_rpow_half hR]

/-- Lower bound on the far part (`lem:cm_far_lower`). There is `C_F > 0` such that for `R ≥ 2`
and `‖s‖ ≤ 2R`, `∑_{‖ρ_i‖ > 4R} log ‖E₁(s/ρ_i)‖ ≥ -C_F R^{3/2}`. -/
theorem exists_tsum_far_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ 2 * R →
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
  obtain ⟨C2, hC2pos, hC2⟩ := exists_sum_inv_norm_sq_riemannXiZeros_tail_le
  refine ⟨8 * C2, by positivity, fun R hR s hs ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hsublog := (summable_log_norm_weierstrassE1 riemannXiZeros
    summable_inv_norm_sq_riemannXiZeros s).subtype {i | 4 * R < ‖riemannXiZeros i‖}
  have hsubinv := (summable_inv_norm_sq_riemannXiZeros.subtype
    {i | 4 * R < ‖riemannXiZeros i‖}).mul_left (-16 * R ^ 2)
  -- Termwise `log ‖E₁(s/ρ)‖ ≥ -4‖s/ρ‖² ≥ -16R²‖ρ⁻¹‖²`, valid since `‖s/ρ‖ ≤ 1/2` on the far set.
  have hterm : ∀ i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
      -16 * R ^ 2 * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2
        ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
    intro i
    set ρ := riemannXiZeros (i : RiemannXiZerosIndex) with hρ
    have hρpos : (0 : ℝ) < ‖ρ‖ := lt_trans h4R i.2
    refine le_trans ?_ (neg_le_log_norm_weierstrassE1
      (show ‖s / ρ‖ ≤ 1 / 2 by rw [norm_div, div_le_iff₀ hρpos]; linarith [i.2]))
    rw [show ‖s / ρ‖ ^ 2 = ‖s‖ ^ 2 * ‖ρ⁻¹‖ ^ 2 by rw [norm_div, norm_inv]; ring]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * R ^ 2 - 4 * ‖s‖ ^ 2 by
      nlinarith [hs, norm_nonneg s, hRpos]) (sq_nonneg ‖ρ⁻¹‖)]
  refine le_trans ?_
    (Summable.tsum_le_tsum (L := SummationFilter.unconditional _) hterm hsubinv hsublog)
  rw [tsum_mul_left]
  calc -(8 * C2 * R ^ (3 / 2 : ℝ))
      = -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ)) := by
        rw [show -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ))
          = -(C2 * (16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ))) by ring, far_rpow_id hRpos]; ring
    _ ≤ -16 * R ^ 2 * ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonpos_left (hC2 (4 * R) h4R) (by nlinarith [sq_nonneg R, hRpos])

/-- Lower bound on the near part on a good circle (`lem:cm_near_lower`). There is `C_N > 0` such
that for every `R ≥ 2` there is `R' ∈ [R, 2R]` for which, for all `s` with `‖s‖ = R'`: (1) `s ≠ ρ_i`
for every near `i` (`‖ρ_i‖ ≤ 4R`), and (2) `∑_{near} log ‖E₁(s/ρ_i)‖ ≥ -C_N R^{3/2}`. -/
theorem exists_finset_near_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (∀ i : RiemannXiZerosIndex, ‖riemannXiZeros i‖ ≤ 4 * R → s ≠ riemannXiZeros i) ∧
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset,
          Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
  obtain ⟨Cn, hCnpos, hCn⟩ := exists_card_riemannXiZeros_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_inv_norm_riemannXiZeros_le
  set Clog : ℝ := Real.log (256 * Cn + 4) + 2 with hClog
  have hlogc : (0 : ℝ) ≤ Real.log (256 * Cn + 4) := Real.log_nonneg (by linarith)
  have hcc : (0 : ℝ) ≤ 12 * Cn * Clog := by rw [hClog]; nlinarith
  refine ⟨4 * C1 + 192 * Cn * Clog, by linarith, fun R hR ↦ ?_⟩
  -- Fix `R ≥ 2`.
  have hRpos : (0 : ℝ) < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  set m := F.card with hm
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set δ : ℝ := R / (4 * ((m : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := div_pos hRpos (by positivity)
  have hδid : δ * (4 * ((m : ℝ) + 1)) = R := by rw [hδ]; field_simp
  -- Cardinality of the near set: `m ≤ Cₙ · 4R log (4R)`.
  have hmcard : (m : ℝ) ≤ Cn * (4 * R * Real.log (4 * R)) := by
    rw [hm, hF, ← Set.ncard_eq_toFinset_card _ (finite_setOf_norm_riemannXiZeros_le (4 * R))]
    exact hCn (4 * R) (by linarith)
  -- Radius selection avoiding the near zeros: `2δm < R` leaves room in `[R, 2R]`.
  obtain ⟨R', hR'mem, hR'dist⟩ :=
    exists_mem_Icc_forall_le_dist (S := F.image fun i ↦ ‖riemannXiZeros i‖) (a := R) (b := 2 * R)
      hδpos (by
        have hci : ((F.image fun i ↦ ‖riemannXiZeros i‖).card : ℝ) ≤ (m : ℝ) := by
          rw [hm]; exact_mod_cast Finset.card_image_le
        nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hci), mul_nonneg hδpos.le hmnn])
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  have hR'le : R' ≤ 2 * R := hR'mem.2
  -- Reverse triangle inequality: the circle `‖s‖ = R'` is `δ`-far from every near zero.
  have hdist : ∀ i ∈ F, δ ≤ ‖s - riemannXiZeros i‖ := fun i hiF ↦
    (hR'dist _ (Finset.mem_image_of_mem _ hiF)).trans <| by
      simpa only [hs] using abs_norm_sub_norm_le s (riemannXiZeros i)
  have hne : ∀ i ∈ F, s ≠ riemannXiZeros i := fun i hiF heq ↦ by
    have hd := hdist i hiF; rw [heq, sub_self, norm_zero] at hd; linarith
  refine ⟨fun i hi ↦ hne i (by rw [hF, Set.Finite.mem_toFinset]; exact hi), ?_⟩
  -- `log δ - log (4R) = log (δ / 4R) = -log (16 (m+1))`.
  have hlogd : Real.log δ - Real.log (4 * R) = -Real.log (16 * ((m : ℝ) + 1)) := by
    rw [← Real.log_div hδpos.ne' (by positivity), ← Real.log_inv]
    congr 1
    rw [hδ]; field_simp; ring
  -- Termwise: `log ‖E₁(s/ρ)‖ = log ‖s - ρ‖ - log ‖ρ‖ + Re (s/ρ) ≥ log δ - log (4R) - 2R‖ρ⁻¹‖`.
  have hpt : ∀ i ∈ F, Real.log δ - Real.log (4 * R) - 2 * R * ‖(riemannXiZeros i)⁻¹‖
      ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
    intro i hiF
    set ρ := riemannXiZeros i with hρ
    have hρne : ρ ≠ 0 := riemannXiZeros_ne_zero i
    have hi4R : ‖ρ‖ ≤ 4 * R := by have h := hiF; rw [hF, Set.Finite.mem_toFinset] at h; exact h
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
    have hsne : s ≠ ρ := hne i hiF
    rw [log_norm_weierstrassE1 (fun h ↦ hsne ((div_eq_one_iff_eq hρne).mp h)),
      show ‖(1 : ℂ) - s / ρ‖ = ‖s - ρ‖ / ‖ρ‖ by
        rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ by rw [sub_div, div_self hρne], norm_div,
          norm_sub_rev],
      Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsne)) hρpos.ne']
    -- `Re (s/ρ) ≥ -‖s/ρ‖ ≥ -2R‖ρ⁻¹‖`, and `log ‖s - ρ‖ ≥ log δ`, `log ‖ρ‖ ≤ log (4R)`.
    have hb2 : ‖s / ρ‖ ≤ 2 * R * ‖ρ⁻¹‖ := by
      rw [norm_div, norm_inv, hs, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hR'le (by positivity)
    linarith [Real.log_le_log hδpos (hdist i hiF), Real.log_le_log hρpos hi4R,
      (abs_le.mp (Complex.abs_re_le_norm (s / ρ))).1]
  -- Sum the termwise bound, splitting off the constant part.
  refine le_trans ?_ (Finset.sum_le_sum hpt)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hlogd, mul_neg]
  -- The head sum: `2R ∑_{near} ‖ρ⁻¹‖ ≤ 2R · C₁(4R)^{1/2} = 4 C₁ R^{3/2}`.
  have h2Rsum : 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖ ≤ 4 * C1 * R ^ (3 / 2 : ℝ) :=
    calc 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖
        ≤ 2 * R * (C1 * (4 * R) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [hF]; exact hC1 (4 * R) (by linarith)) (by linarith)
      _ = C1 * (2 * R * (4 * R) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * C1 * R ^ (3 / 2 : ℝ) := by rw [near_rpow_id hRpos]; ring
  -- The log term: `m log (16(m+1)) ≤ 12 Cₙ R (log R + 1) · Clog (log R + 1) ≤ 192 Cₙ Clog R^{3/2}`.
  have hmlog : (m : ℝ) * Real.log (16 * ((m : ℝ) + 1)) ≤ 192 * Cn * Clog * R ^ (3 / 2 : ℝ) := by
    have hCn4R : (0 : ℝ) ≤ Cn * (4 * R) := by positivity
    have hm12 : (m : ℝ) ≤ 12 * Cn * R * (Real.log R + 1) := by
      have h : Real.log (4 * R) ≤ 3 * (Real.log R + 1) := by
        rw [Real.log_mul (by norm_num) hRpos.ne']
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hm16 : (m : ℝ) ≤ 16 * Cn * R ^ 2 := by
      have h : Real.log (4 * R) ≤ 4 * R :=
        by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * R by linarith)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hlogm : Real.log (16 * ((m : ℝ) + 1)) ≤ Clog * (Real.log R + 1) := by
      have hmono := Real.log_le_log (show (0 : ℝ) < 16 * ((m : ℝ) + 1) by positivity)
        (show 16 * ((m : ℝ) + 1) ≤ (256 * Cn + 4) * R ^ 2 by nlinarith [hm16])
      rw [Real.log_mul (by positivity) (by positivity : (R : ℝ) ^ 2 ≠ 0), Real.log_pow] at hmono
      rw [hClog]
      push_cast at hmono ⊢
      nlinarith [mul_nonneg hlogc hlogR]
    have hRL2 : R * (Real.log R + 1) ^ 2 ≤ 16 * R ^ (3 / 2 : ℝ) := by
      rw [← self_mul_rpow_half hRpos]
      nlinarith [Real.log_add_one_sq_le hR1, hRpos]
    have hstep := mul_le_mul hm12 hlogm (Real.log_nonneg (by linarith))
      (by positivity : (0 : ℝ) ≤ 12 * Cn * R * (Real.log R + 1))
    nlinarith [mul_le_mul_of_nonneg_left hRL2 hcc]
  linarith only [hmlog, h2Rsum]

/-! ### Assembly: the minimum-modulus selection -/

/-- Minimum-modulus lower bound for the canonical product (`thm:cm_minmod`, `lem:hf_minmod`).
There is `C' > 0` such that for every `R ≥ 2` there is `R' ∈ [R, 2R]` with `P(s) ≠ 0` and
`log ‖P(s)‖ ≥ -C' R^{3/2}` for all `‖s‖ = R'`, where
`P = riemannXiCanonicalProduct riemannXiZeros`. -/
theorem exists_circle_log_norm_riemannXiCanonicalProduct_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      riemannXiCanonicalProduct riemannXiZeros s ≠ 0 ∧
        -(C * R ^ (3 / 2 : ℝ)) ≤ Real.log ‖riemannXiCanonicalProduct riemannXiZeros s‖ := by
  obtain ⟨CF, hCFpos, hCF⟩ := exists_tsum_far_log_norm_weierstrassE1_ge
  obtain ⟨CN, hCNpos, hCN⟩ := exists_finset_near_log_norm_weierstrassE1_ge
  refine ⟨CF + CN, by linarith, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hCN R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hne_near, hnear⟩ := hR' s hs
  have hs2R : ‖s‖ ≤ 2 * R := by rw [hs]; exact hR'mem.2
  have hsum := summable_inv_norm_sq_riemannXiZeros
  have hsumlog := summable_log_norm_weierstrassE1 riemannXiZeros hsum s
  -- No zero lies on the circle: near zeros are avoided by construction, far ones by modulus.
  have hsne : ∀ i, s ≠ riemannXiZeros i := by
    intro i
    rcases le_or_gt ‖riemannXiZeros i‖ (4 * R) with hle | hlt
    · exact hne_near i hle
    · intro heq
      rw [← heq, hs] at hlt
      linarith [hR'mem.2]
  refine ⟨riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros hsum hsne, ?_⟩
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  -- The complement of the near finset is the far set, so the far bound applies to the tail.
  have hfar : -(CF * R ^ (3 / 2 : ℝ))
      ≤ ∑' x : ↥((↑F : Set RiemannXiZerosIndex)ᶜ),
          Real.log ‖weierstrassE1 (s / riemannXiZeros (x : RiemannXiZerosIndex))‖ := by
    rw [show ((↑F : Set RiemannXiZerosIndex)ᶜ) = {i | 4 * R < ‖riemannXiZeros i‖} by
      rw [hF, Set.Finite.coe_toFinset]
      ext i; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
    exact hCF R hR s hs2R
  rw [log_norm_riemannXiCanonicalProduct riemannXiZeros hsum hsne,
    ← hsumlog.sum_add_tsum_compl (s := F)]
  linarith [hnear, hfar]

