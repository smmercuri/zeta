/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Bound
public import Zeta.RiemannSiegel.Inner

/-!
# The outer saddle-point estimate

Companion to `Zeta/RiemannSiegel/Inner.lean`: the region `|w| > W` of the contour, `W` the splitting
radius `Zeta.RiemannSiegel.splitRadius`, `W = T^{1/12}` (`riemann_siegel_first.tex`,
`lem:rsf_outer`). There the saddle discrepancy `Δ` is not small, so `e^Δ` and `1` are bounded
separately, the first by the order-zero Gaussian majorant
`Zeta.RiemannSiegel.norm_contourIntegrand_le` for the true integrand and the second by the
Gaussian numerator of the model. Both tails are super-polynomially small, and the
whole estimate is a `T`-uniform `T^{-1/2}`.

As in the inner region, the uniformity in `T` is obtained by substituting `√T = W^6`
(`splitRadius_pow_six`) and `W ≥ 3.16` (`le_splitRadius`): what has to be proved is the
single-variable inequality `320 W^6 ≤ e^{πW²/2}`, and that follows from the fourteenth term of
the exponential series.

## Main results

* `Zeta.RiemannSiegel.norm_integral_outer_le` (`riemann_siegel_first.tex`, `lem:rsf_outer`): the
  outer integral is at most `T^{-1/2}`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The uniformity in `T` of the outer estimate, as a polynomial inequality in `W = T^{1/12}`
alone. -/
private theorem mul_pow_six_le_exp {W : ℝ} (hW : (3.16 : ℝ) ≤ W) :
    320 * W ^ 6 ≤ Real.exp (π * W ^ 2 / 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (by norm_num) hW
  have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hfact : ((Nat.factorial 14 : ℕ) : ℝ) = 87178291200 := by
    norm_num [Nat.factorial]
  have hy : (0 : ℝ) ≤ π * W ^ 2 / 2 := by positivity
  -- the fourteenth term of the exponential series
  refine le_trans ?_ (Real.pow_div_factorial_le_exp (π * W ^ 2 / 2) hy 14)
  rw [hfact, le_div_iff₀ (by norm_num : (0 : ℝ) < 87178291200),
    show (π * W ^ 2 / 2) ^ 14 = π ^ 14 * W ^ 6 * W ^ 22 / 2 ^ 14 by ring,
    le_div_iff₀ (by norm_num : (0 : ℝ) < 2 ^ 14)]
  have hπ14 : (3.14 : ℝ) ^ 14 ≤ π ^ 14 := pow_le_pow_left₀ (by norm_num) hπ 14
  have hW22 : (3.16 : ℝ) ^ 22 ≤ W ^ 22 := pow_le_pow_left₀ (by norm_num) hW 22
  have hstep : (320 : ℝ) * 87178291200 * 2 ^ 14 ≤ π ^ 14 * W ^ 22 :=
    le_trans (by norm_num) (mul_le_mul hπ14 hW22 (by positivity) (by positivity))
  calc 320 * W ^ 6 * 87178291200 * 2 ^ 14
      = 320 * 87178291200 * 2 ^ 14 * W ^ 6 := by ring
    _ ≤ π ^ 14 * W ^ 22 * W ^ 6 := mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = π ^ 14 * W ^ 6 * W ^ 22 := by ring

/-- The pointwise majorant for the true integrand: renormalised by the saddle factor, the
Riemann–Siegel integrand along `L(ν + ½)` is a Gaussian of half the model's width. -/
private theorem norm_modelIntegrand_mul_exp_saddleDiscrepancy_le {t : ℝ} (ht : 0 < t) {ν : ℕ}
    (hS : (1000 : ℝ) ≤ Real.sqrt (t / (2 * π))) (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) (w : ℝ) :
    ‖modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w))‖
      ≤ 1100 * Real.exp (-(π / 2) * w ^ 2) := by
  have hπ1 : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hπ2 : π < 3.1416 := Real.pi_lt_d4
  have hT0 : (0 : ℝ) < t / (2 * π) := by positivity
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  have hSsq : S ^ 2 = t / (2 * π) := Real.sq_sqrt hT0.le
  set a : ℝ := (ν : ℝ) + 1 / 2 with hadef
  have ha0 : (0 : ℝ) < a := by rw [hadef]; positivity
  have haS1 : a - 1 / 2 ≤ S := by rw [hadef]; linarith
  have haS2 : S ≤ a + 1 / 2 := by rw [hadef]; linarith
  have ha1 : (999.5 : ℝ) ≤ a := by linarith
  have ha : a = ((ν : ℤ) : ℝ) + 1 / 2 := by rw [hadef]; push_cast; ring
  -- the crossing point is far enough out that the order-zero majorant applies
  have hTa : t / (2 * π) ≤ 2 * a ^ 2 := by rw [← hSsq]; nlinarith
  -- and near enough to the saddle that its Gaussian offset `B` is bounded
  have hTa2 : |t / (2 * π) - a ^ 2| ≤ a + 1 / 4 :=
    abs_sub_sq_le hSsq (by linarith) (by linarith) (by linarith)
  -- the Gaussian majorant of the order-zero bound, with half its exponent traded for a constant
  have hAM : -(π * w ^ 2) + 2 * π * |t / (2 * π) - a ^ 2| / a * |w|
      ≤ 7 + -(π / 2) * w ^ 2 := by
    have hB : 2 * π * |t / (2 * π) - a ^ 2| / a ≤ 6.29 := by
      rw [div_le_iff₀ ha0]
      nlinarith [mul_le_mul_of_nonneg_left hTa2 (by positivity : (0 : ℝ) ≤ 2 * π),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 3.1416 - π) (by linarith : (0 : ℝ) ≤ a)]
    nlinarith [mul_le_mul_of_nonneg_right hB (abs_nonneg w), sq_nonneg (|w| - 2.11),
      abs_nonneg w, sq_abs w, mul_nonneg (by linarith : (0 : ℝ) ≤ π - 3.1415) (sq_nonneg w)]
  -- the constants: the fourth root of two against the square root, and `T ≤ 1.001⁴a²`
  have hKR : 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) / Real.sqrt 2
      ≤ 1.001 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
    have h2rpow : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hcore : a ^ (-(1 / 2) : ℝ) ≤ 1.001 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) :=
      rpow_neg_half_le_mul_rpow_neg_quarter ha0 hT0 (by norm_num)
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 999.5) ha0.le])
    rw [div_le_iff₀ hs2]
    nlinarith [Real.rpow_nonneg ha0.le (-(1 / 2) : ℝ), Real.rpow_nonneg hT0.le (-(1 / 4) : ℝ),
      hs2.le]
  -- the numerical constant `e^7`
  have hE : Real.exp 7 ≤ 1097 := by
    rw [show (7 : ℝ) = (7 : ℕ) by norm_num, ← Real.exp_one_pow]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 7).trans (by norm_num)
  rw [norm_modelIntegrand_mul_exp_saddleDiscrepancy ht ν w,
    div_le_iff₀ (Real.rpow_pos_of_pos hT0 _)]
  calc ‖contourIntegrand (1 / 2 + t * I) a w‖
      ≤ 2 ^ (1 / 4 : ℝ) * a ^ (-(1 / 2) : ℝ) / Real.sqrt 2 *
        Real.exp (-(π * w ^ 2) + 2 * π * |t / (2 * π) - a ^ 2| / a * |w|) :=
        norm_contourIntegrand_le ht.le ha ha0 hTa w
    _ ≤ 1.001 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) * (Real.exp 7 * Real.exp (-(π / 2) * w ^ 2)) := by
        refine mul_le_mul hKR ?_ (Real.exp_nonneg _) (by positivity)
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 hAM
    _ = 1.001 * Real.exp 7 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * Real.exp (-(π / 2) * w ^ 2)) := by
        ring
    _ ≤ 1100 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * Real.exp (-(π / 2) * w ^ 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1100 * Real.exp (-(π / 2) * w ^ 2) * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by ring

/-- The pointwise majorant for the model integrand on the outer region `|w| > W`. -/
private theorem norm_modelIntegrand_le_outer {p W w : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2)
    (hW : (1 : ℝ) ≤ W) (hw : W < |w|) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 1.93 * (Real.exp (-(π * W ^ 2))
        * Real.exp (-(2 * π) * (w + (1 / 2 - p) / 2) ^ 2)) := by
  have hπ := Real.pi_pos
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2' : (1.414 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  -- the Gaussian numerator, of peak `e^{π/4}` and centre `-(½ - p)/2`
  have h8 := norm_modelIntegrand_le_exp_neg_mul_sq hκ w
  -- the shifted centre is still at distance at least `W - ¼` from the origin
  have h1 : |w| ≤ |w + (1 / 2 - p) / 2| + |(1 / 2 - p) / 2| := by
    simpa using abs_add_le (w + (1 / 2 - p) / 2) (-((1 / 2 - p) / 2))
  have hd : |(1 / 2 - p) / 2| ≤ 1 / 4 := by rw [abs_div, abs_two]; linarith
  have habs : W - 1 / 4 ≤ |w + (1 / 2 - p) / 2| := by linarith
  have h2u : W ^ 2 ≤ 2 * (w + (1 / 2 - p) / 2) ^ 2 := by
    rw [← sq_abs (w + (1 / 2 - p) / 2)]
    nlinarith [abs_nonneg (w + (1 / 2 - p) / 2)]
  have hexp : Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)
      ≤ Real.exp (-(π * W ^ 2)) * Real.exp (-(2 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hπ.le (sub_nonneg.2 h2u)])
  have hconst : Real.exp (π / 4) / Real.sqrt 2 ≤ 1.93 := by
    rw [div_le_iff₀ hs2]
    nlinarith [(Real.exp_le_exp.2 (by linarith [Real.pi_lt_d4] : π / 4 ≤ 1)).trans
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 2.72)]
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (π / 4) * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) / Real.sqrt 2 := h8
    _ = Real.exp (π / 4) / Real.sqrt 2 * Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) := by
        ring
    _ ≤ 1.93 * (Real.exp (-(π * W ^ 2))
          * Real.exp (-(2 * π) * (w + (1 / 2 - p) / 2) ^ 2)) :=
        mul_le_mul hconst hexp (Real.exp_nonneg _) (by norm_num)

/-- The outer saddle-point estimate (`riemann_siegel_first.tex`, `lem:rsf_outer`): the
contribution to the model integral of the region `|w| > W = T^{1/12}`, away from the saddle. -/
theorem norm_integral_outer_le {t : ℝ} (ht : 10 ^ 6 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in (Set.Icc (-splitRadius t) (splitRadius t))ᶜ,
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 1 / Real.sqrt (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have hπ1 : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2' : Real.sqrt 2 ≤ 1.415 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hS1000 : (1000 : ℝ) ≤ Real.sqrt (t / (2 * π)) :=
    Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hκ : |1 / 2 - (Real.sqrt (t / (2 * π)) - ν)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  -- the two pointwise majorants, and integrability of the perturbed model integrand
  have hGpt := norm_modelIntegrand_mul_exp_saddleDiscrepancy_le ht0 hS1000 hν hν'
  have hFint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν
  -- abbreviations for the splitting radius, the saddle `√T` and the fractional part `p`
  set W : ℝ := splitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  have hW0 : 0 < W := by rw [hWdef]; exact splitRadius_pos ht0
  have hW6 : W ^ 6 = S := by rw [hWdef, hSdef]; exact splitRadius_pow_six ht0
  have hW316 : (3.16 : ℝ) ≤ W := by
    rw [hWdef]
    exact le_splitRadius (by norm_num) (le_trans (by norm_num) ht)
  clear_value p S W
  have hS0 : (0 : ℝ) < S := by linarith
  -- the two Gaussian majorants
  set majG : ℝ → ℝ := fun w ↦ 1100 * Real.exp (-(π / 2) * w ^ 2) with hmajG
  set majH : ℝ → ℝ := fun w ↦ 1.93 * (Real.exp (-(π * W ^ 2))
    * Real.exp (-(2 * π) * (w + (1 / 2 - p) / 2) ^ 2)) with hmajH
  have hmajGint : Integrable majG :=
    (integrable_exp_neg_mul_sq (b := π / 2) (by positivity)).const_mul _
  have hmajHint : Integrable majH :=
    (((integrable_exp_neg_mul_sq (b := 2 * π)
      (by positivity)).comp_add_right ((1 / 2 - p) / 2)).const_mul _).const_mul _
  -- the two tail integrals
  have htailG : ∫ w in (Set.Icc (-W) W)ᶜ, majG w ≤ 223 * Real.exp (-(π / 2) * W ^ 2) := by
    rw [hmajG, integral_const_mul]
    refine (mul_le_mul_of_nonneg_left (integral_compl_Icc_exp_neg_mul_sq_le (b := π / 2)
      (by positivity) hW0) (by norm_num)).trans ?_
    have hpiW : (1100 : ℝ) ≤ 223 * (π / 2 * W) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hπ1) (sub_nonneg.2 hW316)]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < π / 2 * W)]
    nlinarith [Real.exp_pos (-(π / 2) * W ^ 2)]
  have htailH : ∫ w in (Set.Icc (-W) W)ᶜ, majH w ≤ 1.37 * Real.exp (-(π / 2) * W ^ 2) := by
    have hval : ∫ w : ℝ, majH w
        = 1.93 * (Real.exp (-(π * W ^ 2)) * Real.sqrt (π / (2 * π))) := by
      rw [hmajH, integral_const_mul, integral_const_mul,
        show (∫ w : ℝ, Real.exp (-(2 * π) * (w + (1 / 2 - p) / 2) ^ 2))
          = ∫ w : ℝ, (fun u : ℝ ↦ Real.exp (-(2 * π) * u ^ 2)) (w + (1 / 2 - p) / 2) from rfl,
        integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(2 * π) * u ^ 2)) ((1 / 2 - p) / 2),
        integral_gaussian]
    have hsqrt : Real.sqrt (π / (2 * π)) ≤ 0.708 :=
      (Real.sqrt_le_left (by norm_num)).2 (by rw [div_le_iff₀ (by positivity)]; nlinarith [hπ1])
    have hEE : Real.exp (-(π * W ^ 2)) ≤ Real.exp (-(π / 2) * W ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, sq_nonneg W])
    refine (setIntegral_le_integral hmajHint (.of_forall fun w ↦ by positivity)).trans ?_
    rw [hval]
    nlinarith [Real.exp_pos (-(π * W ^ 2)), Real.sqrt_nonneg (π / (2 * π))]
  calc ‖(1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖ :=
        norm_one_add_I_mul_integral_le _
    -- the pointwise bound on the outer region
    _ ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, (majG w + majH w) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          (hmajGint.add hmajHint).integrableOn measurableSet_Icc.compl fun w hw ↦ ?_) hs2.le
        simp only [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le] at hw
        exact (norm_mul_sub_one_le _ _).trans
          (add_le_add (hGpt w) (norm_modelIntegrand_le_outer hκ (by linarith) hw))
    _ ≤ 320 * Real.exp (-(π / 2) * W ^ 2) := by
        rw [integral_add hmajGint.integrableOn hmajHint.integrableOn]
        nlinarith [add_le_add htailG htailH, (Real.exp_pos (-(π / 2) * W ^ 2)).le]
    -- and the final numerical step: `320 e^{-πW²/2} ≤ W^{-6} = T^{-1/2}`
    _ ≤ 1 / S := by
        rw [show Real.exp (-(π / 2) * W ^ 2) = 1 / Real.exp (π * W ^ 2 / 2) by
              rw [one_div, ← Real.exp_neg]; congr 1; ring,
          ← hW6, mul_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
        linarith [mul_pow_six_le_exp hW316]

end Zeta.RiemannSiegel
