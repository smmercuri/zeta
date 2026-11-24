/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# The genus-one Weierstrass elementary factor

The elementary factor `E₁(w) = (1 - w) eᵂ`, its bounds near `w = 0`, and the genus-one canonical
product `P(s) = ∏ᵢ E₁(s/ρᵢ)` assembled from it (`hadamard_factorization.tex`).

## Main results

* `weierstrassE1` (`def:hf_elem`): the elementary factor.
* `weierstrassE1_eq_zero_iff`: `E₁(w) = 0 ↔ w = 1`.
* `Complex.norm_log_one_sub_add_self_le`: `‖Log (1 - w) + w‖ ≤ ‖w‖²` for `‖w‖ ≤ 1/2`.
* `log_norm_weierstrassE1`: `Real.log ‖E₁(w)‖ = Real.log ‖1 - w‖ + w.re`.
* `norm_weierstrassE1_sub_one_le` (`lem:hf_elem_bound`): `‖E₁(w) - 1‖ ≤ 2 ‖w‖²` for `‖w‖ ≤ 1/2`.
* `riemannXiCanonicalProduct` (`def:hf_prod`): the canonical product `P`.
* `hasProdLocallyUniformlyOn_riemannXiCanonicalProduct` (`lem:hf_prod_summable`): the product
  converges locally uniformly on `ℂ`.
* `riemannXiCanonicalProduct_ne_zero_of_forall_ne`: `P` is zero-free away from the `ρᵢ`.
* `log_norm_riemannXiCanonicalProduct`, `log_norm_riemannXiCanonicalProduct_eq_tsum`:
  `log ‖P(s)‖` as a sum over the factors.
* `log_norm_riemannXiCanonicalProduct_le` (`lem:hf_prod_order`): order-`3/2` growth of `log ‖P‖`.
* `analyticOrderNatAt_riemannXiCanonicalProduct` (`lem:hf_prod_entire`): the zeros of `P`, with
  multiplicity, are exactly the `ρᵢ`.
-/
@[expose] public section


/-- The genus-one Weierstrass elementary factor `E₁(w) = (1 - w) eᵂ`. -/
noncomputable def weierstrassE1 (w : ℂ) : ℂ := (1 - w) * Complex.exp w

/-- `E₁(0) = 1`. -/
@[simp] lemma weierstrassE1_zero : weierstrassE1 0 = 1 := by simp [weierstrassE1]

/-- The elementary factor is continuous. -/
@[continuity, fun_prop]
lemma continuous_weierstrassE1 : Continuous weierstrassE1 := by
  unfold weierstrassE1; fun_prop

/-- The elementary factor `E₁(w) = (1 - w) eᵂ` is entire. -/
@[fun_prop]
lemma differentiable_weierstrassE1 : Differentiable ℂ weierstrassE1 := by
  unfold weierstrassE1; fun_prop

/-- `E₁(w)` is the exponential of the branch-free logarithm `Log (1 - w) + w` (for `w ≠ 1`). -/
lemma weierstrassE1_eq_exp_log {w : ℂ} (hw : w ≠ 1) :
    weierstrassE1 w = Complex.exp (Complex.log (1 - w) + w) := by
  rw [weierstrassE1, Complex.exp_add, Complex.exp_log (sub_ne_zero.mpr hw.symm), mul_comm]

/-- The elementary factor vanishes exactly at `w = 1`: `E₁(w) = 0 ↔ w = 1`. -/
@[simp] lemma weierstrassE1_eq_zero_iff {w : ℂ} : weierstrassE1 w = 0 ↔ w = 1 := by
  rw [weierstrassE1, mul_eq_zero, or_iff_left (Complex.exp_ne_zero w), sub_eq_zero, eq_comm]

/-- The elementary factor is nonzero away from `w = 1`. -/
lemma weierstrassE1_ne_zero {w : ℂ} (hw : w ≠ 1) : weierstrassE1 w ≠ 0 :=
  weierstrassE1_eq_zero_iff.not.mpr hw

/-- `‖Log (1 - w) + w‖ ≤ ‖w‖²` for `‖w‖ ≤ 1/2` (`lem:hf_elem_bound`). -/
lemma Complex.norm_log_one_sub_add_self_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have key := Complex.norm_log_one_add_sub_self_le (z := -w) (by rwa [norm_neg])
  rw [show (1 : ℂ) + -w = 1 - w by ring, sub_neg_eq_add, norm_neg] at key
  refine key.trans ?_
  have hpos : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos two_pos]
    linarith
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖w‖ ^ 2 := by ring

/-- The log-modulus of the elementary factor splits branch-freely:
`Real.log ‖E₁(w)‖ = Real.log ‖1 - w‖ + Re w` (for `w ≠ 1`). -/
lemma log_norm_weierstrassE1 {w : ℂ} (hw : w ≠ 1) :
    Real.log ‖weierstrassE1 w‖ = Real.log ‖1 - w‖ + w.re := by
  have h1 : ‖(1 : ℂ) - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw.symm)
  have h2 : ‖Complex.exp w‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero w)
  rw [weierstrassE1, norm_mul, Real.log_mul h1 h2, Complex.norm_exp, Real.log_exp]

/-- Quadratic bound on the elementary factor near `w = 0`: `‖E₁(w) - 1‖ ≤ 2 ‖w‖²` for
`‖w‖ ≤ 1/2` (`lem:hf_elem_bound`). -/
lemma norm_weierstrassE1_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖weierstrassE1 w - 1‖ ≤ 2 * ‖w‖ ^ 2 := by
  have hne : w ≠ 1 := by rintro rfl; rw [norm_one] at hw; linarith
  rw [weierstrassE1_eq_exp_log hne]
  have hl : ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := Complex.norm_log_one_sub_add_self_le hw
  have hl1 : ‖Complex.log (1 - w) + w‖ ≤ 1 := hl.trans (by nlinarith [norm_nonneg w])
  exact (Complex.norm_exp_sub_one_le hl1).trans (by linarith)

/-- A sub-quadratic upper bound on the log-modulus of the elementary factor, valid for every
`w ≠ 1`: `log ‖E₁(w)‖ ≤ 4 ‖w‖^{3/2}`. -/
lemma log_norm_weierstrassE1_le {w : ℂ} (hw : w ≠ 1) :
    Real.log ‖weierstrassE1 w‖ ≤ 4 * ‖w‖ ^ (3 / 2 : ℝ) := by
  have ht0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  rcases le_or_gt ‖w‖ (1 / 2) with hle | hgt
  · -- `‖w‖ ≤ 1/2`: `log ‖E₁(w)‖ ≤ ‖w‖² ≤ 4 ‖w‖^{3/2}`.
    have hsq : Real.log ‖weierstrassE1 w‖ ≤ ‖w‖ ^ 2 := by
      have he : Real.log ‖weierstrassE1 w‖ = (Complex.log (1 - w) + w).re := by
        rw [log_norm_weierstrassE1 hw, Complex.add_re, Complex.log_re]
      rw [he]
      exact (Complex.re_le_norm _).trans (Complex.norm_log_one_sub_add_self_le hle)
    refine hsq.trans ?_
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · rw [← h0, Real.zero_rpow (by norm_num)]; norm_num
    · have e : ‖w‖ ^ 2 = ‖w‖ ^ (3 / 2 : ℝ) * ‖w‖ ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast ‖w‖ 2, ← Real.rpow_add hpos]; norm_num
      rw [e]
      have hle1 : ‖w‖ ^ (1 / 2 : ℝ) ≤ 4 :=
        (Real.rpow_le_one ht0 (by linarith) (by norm_num)).trans (by norm_num)
      nlinarith [Real.rpow_nonneg ht0 (3 / 2 : ℝ), hle1]
  · -- `1/2 < ‖w‖`: `log ‖E₁(w)‖ ≤ 2 ‖w‖ ≤ 4 ‖w‖^{3/2}`.
    have hpos : (0 : ℝ) < ‖w‖ := by linarith
    have hlin : Real.log ‖weierstrassE1 w‖ ≤ 2 * ‖w‖ := by
      rw [log_norm_weierstrassE1 hw]
      have hlog1 : Real.log ‖1 - w‖ ≤ ‖w‖ := by
        have hb : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by simpa using norm_sub_le (1 : ℂ) w
        have hw0 : (0 : ℝ) < ‖1 - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hw))
        calc Real.log ‖1 - w‖ ≤ Real.log (1 + ‖w‖) := Real.log_le_log hw0 hb
          _ ≤ ‖w‖ := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ‖w‖ by positivity)
              linarith
      have hre : w.re ≤ ‖w‖ := Complex.re_le_norm w
      linarith
    refine hlin.trans ?_
    have e : ‖w‖ ^ (3 / 2 : ℝ) = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one]
    rw [e]
    have hge : (1 / 2 : ℝ) ≤ ‖w‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith [hpos.le, hge]

/-- The derivative of the elementary factor: `E₁'(w) = -w eᵂ`. In particular `E₁'(1) = -e ≠ 0`, so
the zero at `w = 1` is simple. -/
lemma hasDerivAt_weierstrassE1 (w : ℂ) :
    HasDerivAt weierstrassE1 (-w * Complex.exp w) w := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
  exact (h1.mul (Complex.hasDerivAt_exp w)).congr_deriv (by ring)

section CanonicalProduct

variable {ι : Type*} (ρ : ι → ℂ)

/-- The genus-one canonical product `P(s) = ∏ᵢ E₁(s/ρᵢ)` over an enumeration `ρ` of points
(intended: the nontrivial zeros of `ξ`, counted with multiplicity) (`def:hf_prod`). -/
noncomputable def riemannXiCanonicalProduct (s : ℂ) : ℂ :=
  ∏' i, weierstrassE1 (s / ρ i)

/-- `P(0) = 1`. -/
@[simp] lemma riemannXiCanonicalProduct_zero : riemannXiCanonicalProduct ρ 0 = 1 := by
  simp [riemannXiCanonicalProduct]

/-- If `∑ᵢ ‖ρᵢ⁻¹‖² < ∞`, then for every `c > 0` cofinitely many indices satisfy
`‖ρᵢ⁻¹‖ ≤ c`. -/
lemma eventually_norm_inv_le (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ c := by
  filter_upwards [hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (pow_pos hc 2))]
    with i hi
  exact (lt_of_pow_lt_pow_left₀ 2 hc.le hi).le

/-- The quadratic factor bound transported to the argument `s / ρ i`: if `‖s‖‖ρᵢ⁻¹‖ ≤ 1/2` then
`‖E₁(s/ρᵢ) - 1‖ ≤ 2 ‖s‖² ‖ρᵢ⁻¹‖²`. -/
private lemma norm_weierstrassE1_div_sub_one_le {s : ℂ} (i : ι)
    (h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2) :
    ‖weierstrassE1 (s / ρ i) - 1‖ ≤ 2 * ‖s‖ ^ 2 * ‖(ρ i)⁻¹‖ ^ 2 := by
  have hnorm : ‖s / ρ i‖ = ‖s‖ * ‖(ρ i)⁻¹‖ := by rw [div_eq_mul_inv, norm_mul]
  refine (norm_weierstrassE1_sub_one_le (by rw [hnorm]; exact h)).trans_eq ?_
  rw [hnorm, mul_pow]; ring

/-- The norms `‖E₁(s/ρᵢ) - 1‖` are summable (provided `∑ᵢ ‖ρᵢ⁻¹‖² < ∞`). -/
lemma summable_norm_weierstrassE1_sub_one (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Summable fun i => ‖weierstrassE1 (s / ρ i) - 1‖ := by
  have hu : Summable (fun i => 2 * ‖s‖ ^ 2 * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * (‖s‖ + 1)) :=
    eventually_norm_inv_le ρ hsum (by positivity)
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [htail] with i hi
  have h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2 := by
    calc ‖s‖ * ‖(ρ i)⁻¹‖ ≤ ‖s‖ * (1 / (2 * (‖s‖ + 1))) :=
          mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg s]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_weierstrassE1_div_sub_one_le ρ i h

/-- For each `s`, the family `i ↦ E₁(s/ρᵢ)` is multipliable (provided `∑ᵢ ‖ρᵢ⁻¹‖² < ∞`). -/
lemma multipliable_weierstrassE1 (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Multipliable fun i => weierstrassE1 (s / ρ i) := by
  have heq : (fun i => weierstrassE1 (s / ρ i))
      = fun i => 1 + (weierstrassE1 (s / ρ i) - 1) := by funext i; ring
  rw [heq]
  exact multipliable_one_add_of_summable (summable_norm_weierstrassE1_sub_one ρ hsum s)

/-- Local uniform convergence of the canonical product (`lem:hf_prod_summable`). If
`∑ᵢ ‖ρᵢ⁻¹‖² < ∞`, then `∏ᵢ E₁(s/ρᵢ)` converges to `P` locally uniformly on `ℂ`. -/
lemma hasProdLocallyUniformlyOn_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) :
    HasProdLocallyUniformlyOn (fun i s => weierstrassE1 (s / ρ i))
      (riemannXiCanonicalProduct ρ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  -- Enclose the compact set `K` in a closed ball of radius `R ≥ 1`.
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hKR : K ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- The summable dominating sequence.
  have hu : Summable (fun i => 2 * R ^ 2 * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  -- Each factor minus one is continuous.
  have hcts : ∀ i, ContinuousOn (fun s => weierstrassE1 (s / ρ i) - 1) K := fun i => by
    fun_prop
  -- Cofinitely many factors have `‖ρᵢ⁻¹‖ ≤ 1/(2R)`.
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * R) :=
    eventually_norm_inv_le ρ hsum (by positivity)
  -- The eventual domination bound on `K`.
  have hbd : ∀ᶠ i in Filter.cofinite,
      ∀ s ∈ K, ‖weierstrassE1 (s / ρ i) - 1‖ ≤ 2 * R ^ 2 * ‖(ρ i)⁻¹‖ ^ 2 := by
    filter_upwards [htail] with i hi s hs
    have hsR : ‖s‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hKR hs
    have h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2 :=
      (mul_le_mul hsR hi (norm_nonneg _) hRpos.le).trans_eq (by field_simp)
    refine (norm_weierstrassE1_div_sub_one_le ρ i h).trans ?_
    gcongr
  -- Assemble via the dominated infinite-product convergence engine.
  convert Summable.hasProdUniformlyOn_one_add hK hu hbd hcts using 2 with s s i <;>
    simp [riemannXiCanonicalProduct]

/-- The canonical product is entire (entirety half of `lem:hf_prod_entire`): if
`∑ᵢ ‖ρᵢ⁻¹‖² < ∞`, then `P` is differentiable on all of `ℂ`. -/
theorem differentiable_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) :
    Differentiable ℂ (riemannXiCanonicalProduct ρ) := by
  rw [← differentiableOn_univ]
  have h := hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ hsum
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  refine h.differentiableOn (.of_forall fun t => ?_) isOpen_univ
  exact DifferentiableOn.fun_finsetProd fun i _ =>
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn

/-- Under `s ≠ ρᵢ` the argument `s/ρᵢ` of the elementary factor avoids its unique zero at `1`
(both when `ρᵢ = 0`, where `s/ρᵢ = 0`, and when `ρᵢ ≠ 0`, where `s/ρᵢ = 1 ↔ s = ρᵢ`). -/
private lemma div_ne_one_of_forall_ne {s : ℂ} (hs : ∀ i, s ≠ ρ i) (i : ι) : s / ρ i ≠ 1 := by
  rcases eq_or_ne (ρ i) 0 with hρ | hρ
  · rw [hρ, div_zero]; exact zero_ne_one
  · exact fun h => hs i ((div_eq_one_iff_eq hρ).mp h)

/-- The canonical product is zero-free away from the `ρᵢ` (nonvanishing content of
`lem:hf_quot`): if `∑ᵢ ‖ρᵢ⁻¹‖² < ∞` and `s ≠ ρᵢ` for every `i`, then `P(s) ≠ 0`. -/
lemma riemannXiCanonicalProduct_ne_zero_of_forall_ne
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ} (hs : ∀ i, s ≠ ρ i) :
    riemannXiCanonicalProduct ρ s ≠ 0 := by
  -- Each factor is nonzero: `s / ρ i ≠ 1`.
  have hfac : ∀ i, weierstrassE1 (s / ρ i) ≠ 0 :=
    fun i => weierstrassE1_ne_zero (div_ne_one_of_forall_ne ρ hs i)
  -- Summability of the norms of `aᵢ = E₁(s/ρ i) - 1`.
  have hnsum : Summable (fun i => ‖weierstrassE1 (s / ρ i) - 1‖) :=
    summable_norm_weierstrassE1_sub_one ρ hsum s
  -- Recast the product as `∏ᵢ (1 + aᵢ)` and apply the nonvanishing engine.
  have hsplit : ∀ i, (1 : ℂ) + (weierstrassE1 (s / ρ i) - 1) = weierstrassE1 (s / ρ i) :=
    fun i => by ring
  have hcongr : riemannXiCanonicalProduct ρ s = ∏' i, (1 + (weierstrassE1 (s / ρ i) - 1)) := by
    rw [riemannXiCanonicalProduct]; exact tprod_congr fun i => (hsplit i).symm
  rw [hcongr]
  refine tprod_one_add_ne_zero_of_summable (fun i => ?_) hnsum
  rw [hsplit i]; exact hfac i

/-- The logarithms `log ‖E₁(s/ρᵢ)‖` of the factor moduli are summable. -/
lemma summable_log_norm_weierstrassE1 (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Summable fun i => Real.log ‖weierstrassE1 (s / ρ i)‖ := by
  refine (summable_norm_weierstrassE1_sub_one ρ hsum s).summable_log_norm_one_add.congr fun i => ?_
  rw [show (1 : ℂ) + (weierstrassE1 (s / ρ i) - 1) = weierstrassE1 (s / ρ i) from by ring]

/-- The log-modulus of the canonical product as a sum over the factors:
`log ‖P(s)‖ = ∑ᵢ log ‖E₁(s/ρᵢ)‖`, for `s ≠ ρᵢ` (`lem:hf_prod_order`). -/
lemma log_norm_riemannXiCanonicalProduct (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ}
    (hs : ∀ i, s ≠ ρ i) :
    Real.log ‖riemannXiCanonicalProduct ρ s‖ = ∑' i, Real.log ‖weierstrassE1 (s / ρ i)‖ := by
  have hpos : ∀ i, 0 < ‖weierstrassE1 (s / ρ i)‖ :=
    fun i => norm_pos_iff.mpr (weierstrassE1_ne_zero (div_ne_one_of_forall_ne ρ hs i))
  rw [riemannXiCanonicalProduct, (multipliable_weierstrassE1 ρ hsum s).norm_tprod,
    ← Real.rexp_tsum_eq_tprod hpos (summable_log_norm_weierstrassE1 ρ hsum s), Real.log_exp]

/-- The branch-free split form of the log-modulus representation:
`log ‖P(s)‖ = ∑ᵢ (log ‖1 - s/ρᵢ‖ + Re(s/ρᵢ))` (`lem:hf_prod_order`). -/
lemma log_norm_riemannXiCanonicalProduct_eq_tsum
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ} (hs : ∀ i, s ≠ ρ i) :
    Real.log ‖riemannXiCanonicalProduct ρ s‖
      = ∑' i, (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re) := by
  rw [log_norm_riemannXiCanonicalProduct ρ hsum hs]
  exact tsum_congr fun i => log_norm_weierstrassE1 (div_ne_one_of_forall_ne ρ hs i)

/-- Order-`3/2` growth of the canonical product (`lem:hf_prod_order`). If `∑ᵢ ‖ρᵢ⁻¹‖² < ∞`
and `∑ᵢ ‖ρᵢ⁻¹‖^{3/2} < ∞`, there is `C_P > 0` with `log ‖P(s)‖ ≤ C_P ‖s‖^{3/2}` for every `s`.
The two summability hypotheses are redundant (`hsum32` implies `hsum`) but both are threaded, as
the concrete zero-enumeration supplies each directly. -/
theorem log_norm_riemannXiCanonicalProduct_le
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2)
    (hsum32 : Summable fun i => ‖(ρ i)⁻¹‖ ^ (3 / 2 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      Real.log ‖riemannXiCanonicalProduct ρ s‖ ≤ C * ‖s‖ ^ (3 / 2 : ℝ) := by
  set S : ℝ := ∑' i, ‖(ρ i)⁻¹‖ ^ (3 / 2 : ℝ) with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun i => Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨4 * S + 1, by positivity, fun s => ?_⟩
  have hrs : (0 : ℝ) ≤ ‖s‖ ^ (3 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  rcases eq_or_ne s 0 with rfl | hs0
  · -- `s = 0`: `P(0) = 1`, hence `log ‖P(0)‖ = 0 ≤ C · 0`.
    rw [riemannXiCanonicalProduct_zero, norm_one, Real.log_one, norm_zero,
      Real.zero_rpow (by norm_num), mul_zero]
  · by_cases hne : ∀ i, s ≠ ρ i
    · -- generic point: sum the termwise bound.
      rw [log_norm_riemannXiCanonicalProduct ρ hsum hne]
      have hbd : ∀ i, Real.log ‖weierstrassE1 (s / ρ i)‖
          ≤ 4 * ‖s‖ ^ (3 / 2 : ℝ) * ‖(ρ i)⁻¹‖ ^ (3 / 2 : ℝ) := fun i => by
        refine (log_norm_weierstrassE1_le (div_ne_one_of_forall_ne ρ hne i)).trans ?_
        rw [show ‖s / ρ i‖ = ‖s‖ * ‖(ρ i)⁻¹‖ by rw [div_eq_mul_inv, norm_mul],
          Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
        exact le_of_eq (by ring)
      have hsumR : Summable fun i => 4 * ‖s‖ ^ (3 / 2 : ℝ) * ‖(ρ i)⁻¹‖ ^ (3 / 2 : ℝ) :=
        hsum32.mul_left _
      calc ∑' i, Real.log ‖weierstrassE1 (s / ρ i)‖
          ≤ ∑' i, 4 * ‖s‖ ^ (3 / 2 : ℝ) * ‖(ρ i)⁻¹‖ ^ (3 / 2 : ℝ) :=
            (summable_log_norm_weierstrassE1 ρ hsum s).tsum_le_tsum hbd hsumR
        _ = 4 * ‖s‖ ^ (3 / 2 : ℝ) * S := by rw [tsum_mul_left, hS]
        _ ≤ (4 * S + 1) * ‖s‖ ^ (3 / 2 : ℝ) := by nlinarith [hrs, hSnn]
    · -- `s = ρᵢ₀` for some `i₀`: a factor `E₁(1) = 0`, so `P(s) = 0` and `log ‖P(s)‖ = 0`.
      simp only [not_forall, not_not] at hne
      obtain ⟨i₀, hi₀⟩ := hne
      have hi0ne : ρ i₀ ≠ 0 := fun h => hs0 (by rw [hi₀, h])
      have hfac0 : weierstrassE1 (s / ρ i₀) = 0 := by
        rw [hi₀, div_self hi0ne]; exact weierstrassE1_eq_zero_iff.mpr rfl
      have hP0 : riemannXiCanonicalProduct ρ s = 0 :=
        tprod_of_exists_eq_zero ⟨i₀, hfac0⟩
      rw [hP0, norm_zero, Real.log_zero]
      positivity

/-- Order-of-vanishing matching for the canonical product (order half of `lem:hf_prod_entire`):
if `∑ᵢ ‖ρᵢ⁻¹‖² < ∞` and every `ρᵢ ≠ 0`, the analytic order of `P` at `a` equals the number
`#{i | ρᵢ = a}` of indices mapping to `a`. -/
theorem analyticOrderNatAt_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (hρ : ∀ i, ρ i ≠ 0) (a : ℂ) :
    analyticOrderNatAt (riemannXiCanonicalProduct ρ) a = {i | ρ i = a}.ncard := by
  classical
  -- The fibre `{i | ρ i = a}` is finite.
  have hSfin : {i | ρ i = a}.Finite := by
    rcases eq_or_ne a 0 with rfl | ha
    · exact Set.Finite.subset Set.finite_empty fun i hi => absurd hi (hρ i)
    · have hpos : (0 : ℝ) < ‖a⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero ha)
      have hev : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ^ 2 < ‖a⁻¹‖ ^ 2 :=
        hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (pow_pos hpos 2))
      refine (Filter.eventually_cofinite.mp hev).subset ?_
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      rw [hi]
      exact lt_irrefl _
  set S : Finset ι := hSfin.toFinset with hS
  have hSmem : ∀ i, i ∈ S ↔ ρ i = a := fun i => by
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  -- The tail enumeration over the complement of `S`.
  set ρ' : ↥((S : Set ι)ᶜ) → ℂ := fun j => ρ ↑j
  have hsum' : Summable fun j : ↥((S : Set ι)ᶜ) => ‖(ρ' j)⁻¹‖ ^ 2 := hsum.subtype _
  have hTanalytic : AnalyticAt ℂ (riemannXiCanonicalProduct ρ') a :=
    (differentiable_riemannXiCanonicalProduct ρ' hsum').analyticAt a
  have hTne : riemannXiCanonicalProduct ρ' a ≠ 0 := by
    refine riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ' hsum' fun j => ?_
    have hj : (↑j : ι) ∉ S := by
      have h := j.2; rwa [Set.mem_compl_iff, Finset.mem_coe] at h
    exact fun h => hj ((hSmem ↑j).mpr h.symm)
  -- The base factor `s ↦ E₁(s/a)` is analytic at `a`.
  have hg : AnalyticAt ℂ (fun s => weierstrassE1 (s / a)) a :=
    (by fun_prop : Differentiable ℂ fun s => weierstrassE1 (s / a)).analyticAt a
  -- Global factorisation `P = E₁(·/a)^{#S} · (tail)`.
  have hsplit : riemannXiCanonicalProduct ρ
      = (fun s => weierstrassE1 (s / a)) ^ S.card * riemannXiCanonicalProduct ρ' := by
    funext s
    have hmulF : Multipliable
        ((fun i => weierstrassE1 (s / ρ i)) ∘ ((↑) : ↥(S : Set ι) → ι)) :=
      (S.finite_toSet).multipliable (fun i => weierstrassE1 (s / ρ i))
    have hmulT : Multipliable
        ((fun i => weierstrassE1 (s / ρ i)) ∘ ((↑) : ↥((S : Set ι)ᶜ) → ι)) :=
      multipliable_weierstrassE1 ρ' hsum' s
    have key := Multipliable.tprod_mul_tprod_compl hmulF hmulT
    have hhead : ∏' x : ↥(S : Set ι), weierstrassE1 (s / ρ ↑x)
        = weierstrassE1 (s / a) ^ S.card := by
      have h1 : ∏' x : ↥(S : Set ι), weierstrassE1 (s / ρ ↑x)
          = ∏ i ∈ S, weierstrassE1 (s / ρ i) :=
        Finset.tprod_subtype S (fun i => weierstrassE1 (s / ρ i))
      rw [h1, show (∏ i ∈ S, weierstrassE1 (s / ρ i)) = ∏ _i ∈ S, weierstrassE1 (s / a) from
        Finset.prod_congr rfl fun i hi => by rw [(hSmem i).mp hi], Finset.prod_const]
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [show riemannXiCanonicalProduct ρ s = ∏' i, weierstrassE1 (s / ρ i) from rfl, ← key, hhead,
      show riemannXiCanonicalProduct ρ' s = ∏' x : ↥((S : Set ι)ᶜ), weierstrassE1 (s / ρ ↑x)
        from rfl]
  -- The simple zero of `E₁(·/a)` at `a` (only invoked when `a ≠ 0`).
  have horderg : a ≠ 0 → analyticOrderAt (fun s => weierstrassE1 (s / a)) a = 1 := fun ha => by
    refine hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp [div_self ha]
    · have hu : HasDerivAt (fun s : ℂ => s / a) (1 / a) a := (hasDerivAt_id a).div_const a
      have hd := (hasDerivAt_weierstrassE1 _).comp a hu
      rw [show (fun s => weierstrassE1 (s / a)) = weierstrassE1 ∘ (fun s : ℂ => s / a) from rfl,
        hd.deriv]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero ha ha))
        (Complex.exp_ne_zero _)) (one_div_ne_zero ha)
  -- The order of the head factor is `#S`.
  have hhead_order : analyticOrderAt ((fun s => weierstrassE1 (s / a)) ^ S.card) a
      = (S.card : ℕ∞) := by
    rw [analyticOrderAt_pow hg]
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]; simp
    · have ha : a ≠ 0 := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        rw [← (hSmem i).mp hi]; exact hρ i
      rw [horderg ha]; simp
  have hTorder : analyticOrderAt (riemannXiCanonicalProduct ρ') a = 0 :=
    hTanalytic.analyticOrderAt_eq_zero.mpr hTne
  have hmain : analyticOrderAt (riemannXiCanonicalProduct ρ) a = (S.card : ℕ∞) := by
    rw [hsplit, analyticOrderAt_mul (hg.pow S.card) hTanalytic, hhead_order, hTorder, add_zero]
  rw [analyticOrderNatAt, hmain, ENat.toNat_natCast, Set.ncard_eq_toFinset_card _ hSfin, hS]

end CanonicalProduct

