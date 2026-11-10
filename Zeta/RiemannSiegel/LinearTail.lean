/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.InnerSharp

/-!
# The linear term of the sharp saddle estimate outside the inner region

`Zeta.RiemannSiegel.norm_integral_inner_sub_linear_le` subtracts the `T^{-1/2}`-linear part
`P₁(y)/√T` of the saddle discrepancy over the inner region `|w| ≤ W` only. What the assembly needs
subtracted is the *moment*: the same integrand over the whole contour `L(1/2)`, which is
`-M'''(p)/(96π²)` by `Zeta.RiemannSiegel.neg_half_modelMoment_one_sub_eq`. The difference between
the two is the tail estimated here (`riemann_siegel_first.tex`, `lem:rsf_linear_tail`).

The tail is a Gaussian one taken against a cubic in the contour parameter, which is what
`integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le` supplies. At the sharp splitting
radius `W = (√T - 1)/(2√2)` the surviving exponent `4π(W - 1/4)²` grows linearly in `T`, so the
Gaussian factor beats the lone `√T` that the linear term carries and the bound `T^{-1}/200` is
uniform over `T ≥ 16`.

## Main results

* `Zeta.RiemannSiegel.norm_integral_linear_tail_le`
  (`riemann_siegel_first.tex`, `lem:rsf_linear_tail`): outside the inner region the linear term
  contributes at most `T^{-1}/200`;
* `Zeta.RiemannSiegel.norm_integral_linear_add_iteratedDeriv_three_modelIntegral_le`: the same
  estimate in the form the assembly consumes: over the inner region the linear term is
  `-M'''(p)T^{-1/2}/(96π²)` to within `T^{-1}/200`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The pointwise majorant for the linear term: the model integrand against `P₁(y)`, dominated
by the model Gaussian in the centred contour parameter `ξ = w + (1/2 - p)/2` times a cubic in
`|ξ|`. -/
private theorem norm_modelIntegrand_mul_saddleLinear_le {p : ℝ} (hκ : |1 / 2 - p| ≤ 1 / 2)
    (w : ℝ) :
    ‖modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))‖
      ≤ 11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)
          * (27 / 100 + 182 / 100 * |w + (1 / 2 - p) / 2|
              + 445 / 100 * (w + (1 / 2 - p) / 2) ^ 2
              + 593 / 100 * |w + (1 / 2 - p) / 2| ^ 3)) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hπu : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hsp : Real.sqrt 2 * π ≤ 1.41422 * 3.1416 :=
    mul_le_mul hs2u hπu Real.pi_pos.le (by norm_num)
  set u : ℝ := w + (1 / 2 - p) / 2 with hu
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have husq : |u| ^ 2 = u ^ 2 := sq_abs u
  -- the model integrand, dominated by its Gaussian numerator of peak `e^{π/4} ≤ 11/5`
  have h8 : ‖modelIntegrand (p : ℂ) (1 / 2) w‖
      ≤ 11 / 5 / Real.sqrt 2 * Real.exp (-(4 * π) * u ^ 2) :=
    (norm_modelIntegrand_le_exp_neg_mul_sq hκ w).trans (by
      rw [← hu, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs2]
      exact mul_le_mul_of_nonneg_right Real.exp_pi_div_four_le (Real.exp_nonneg _))
  -- the linear part of the discrepancy, as a cubic in the centred parameter
  have hY : ‖line (1 / 2) w - (p : ℂ)‖ ≤ Real.sqrt 2 * |u| + Real.sqrt 2 / 4 := by
    refine (norm_line_sub_ofReal_le' (1 / 2) w p).trans ?_
    rw [show Real.sqrt 2 * |u| + Real.sqrt 2 / 4 = Real.sqrt 2 * (|u| + 1 / 4) by ring]
    exact mul_le_mul_of_nonneg_left (by rw [hu]; linarith) hs2.le
  have hcubic : ‖line (1 / 2) w - (p : ℂ)‖ / 2 + 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
      ≤ 27 / 100 + 182 / 100 * |u| + 445 / 100 * |u| ^ 2 + 593 / 100 * |u| ^ 3 := by
    have hY0 : (0 : ℝ) ≤ ‖line (1 / 2) w - (p : ℂ)‖ := norm_nonneg _
    have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hcube : ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        ≤ 2 * Real.sqrt 2 * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64) := by
      refine (pow_le_pow_left₀ hY0 hY 3).trans (le_of_eq ?_)
      rw [show (Real.sqrt 2 * |u| + Real.sqrt 2 / 4) ^ 3
          = Real.sqrt 2 * Real.sqrt 2 ^ 2
            * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64) by ring, hs2sq]
      ring
    have hcube' : 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        ≤ 4 * Real.sqrt 2 * π / 3 * |u| ^ 3 + Real.sqrt 2 * π * |u| ^ 2
          + Real.sqrt 2 * π / 4 * |u| + Real.sqrt 2 * π / 48 := by
      have h := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 2 * π / 3)
      calc 2 * π / 3 * ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
          ≤ 2 * π / 3 * (2 * Real.sqrt 2
              * (|u| ^ 3 + 3 / 4 * |u| ^ 2 + 3 / 16 * |u| + 1 / 64)) := h
        _ = _ := by ring
    -- the four coefficients, compared once and for all
    have hc0 : Real.sqrt 2 / 8 + Real.sqrt 2 * π / 48 ≤ 27 / 100 := by linarith
    have hc1 : Real.sqrt 2 / 2 + Real.sqrt 2 * π / 4 ≤ 182 / 100 := by linarith
    have hc2 : Real.sqrt 2 * π ≤ 445 / 100 := by linarith
    have hc3 : 4 * Real.sqrt 2 * π / 3 ≤ 593 / 100 := by linarith
    have p1 := mul_le_mul_of_nonneg_right hc1 hu0
    have p2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg |u|)
    have p3 := mul_le_mul_of_nonneg_right hc3 (pow_nonneg hu0 3)
    linarith
  calc ‖modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))‖
      = ‖modelIntegrand (p : ℂ) (1 / 2) w‖ * ‖saddleLinear (line (1 / 2) w - (p : ℂ))‖ :=
        norm_mul _ _
    _ ≤ 11 / 5 / Real.sqrt 2 * Real.exp (-(4 * π) * u ^ 2)
          * (27 / 100 + 182 / 100 * |u| + 445 / 100 * |u| ^ 2 + 593 / 100 * |u| ^ 3) :=
        mul_le_mul h8 ((norm_saddleLinear_le _).trans hcubic) (norm_nonneg _) (by positivity)
    _ = _ := by rw [husq]; ring

/-- The radius `A = W - 1/4` surviving the recentring of the model Gaussian is at least
`81/100` above the threshold `T ≥ 16`. -/
private theorem le_sharpSplitRadius_sub_quarter {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    81 / 100 ≤ sharpSplitRadius t - 1 / 4 := by
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  rw [sharpSplitRadius, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith

/-- The numerical bound closing the linear tail estimate: past `A = 81/100` the Gaussian factor
`e^{-4πA²}` beats the single power of `√T` that the linear term carries. -/
private theorem linear_tail_constant_le {S A : ℝ} (hS : 0 ≤ S) (hA : 81 / 100 ≤ A)
    (hSA : S ≤ 5 * A) :
    S * (Real.exp (-(4 * π) * A ^ 2)
        * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))
      ≤ π / 110 := by
  have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hA0 : (0 : ℝ) < A := by linarith
  -- the tail polynomial is dominated by a single monomial
  have hP : 27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2
      ≤ 27 * A ^ 2 := by
    have h1 : 27 / 100 / A ≤ 1 / 3 := by
      rw [div_le_div_iff₀ hA0 (by norm_num)]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hA0.le]
  -- `A³e^{-4πA²}` is decreasing past `81/100`, where already `4π(81/100)² ≥ 3`
  have hmono : A ^ 3 * Real.exp (-(4 * π) * A ^ 2)
      ≤ (81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) :=
    pow_mul_exp_neg_mul_sq_le (by positivity) (by norm_num) (by push_cast; nlinarith) hA
  -- and at `A = 81/100` the Gaussian is already smaller than `e^{-8}`
  have hnum : 135 * ((81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2))
      ≤ π / 110 := by
    have hthr : Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2) * 2900 ≤ 1 := by
      rw [show -(4 * π) * (81 / 100 : ℝ) ^ 2 = -(4 * π * (81 / 100 : ℝ) ^ 2) by ring]
      exact exp_neg_mul_le_one (n := 8) (by norm_num) (by push_cast; nlinarith)
    nlinarith [Real.exp_pos (-(4 * π) * (81 / 100 : ℝ) ^ 2)]
  calc S * (Real.exp (-(4 * π) * A ^ 2)
        * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))
      ≤ S * (Real.exp (-(4 * π) * A ^ 2) * (27 * A ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le) hS
    _ ≤ 5 * A * (Real.exp (-(4 * π) * A ^ 2) * (27 * A ^ 2)) :=
        mul_le_mul_of_nonneg_right hSA (by positivity)
    _ = 135 * (A ^ 3 * Real.exp (-(4 * π) * A ^ 2)) := by ring
    _ ≤ 135 * ((81 / 100 : ℝ) ^ 3 * Real.exp (-(4 * π) * (81 / 100 : ℝ) ^ 2)) := by gcongr
    _ ≤ π / 110 := hnum

/-- The linear term outside the inner region (`riemann_siegel_first.tex`,
`lem:rsf_linear_tail`): over `|w| > W = (√T - 1)/(2√2)` the `T^{-1/2}`-linear part `P₁(y)/√T` of
the saddle discrepancy contributes at most `T^{-1}/200`. -/
theorem norm_integral_linear_tail_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * ∫ w in (Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t))ᶜ,
        modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
              / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 1 / 200 / (t / (2 * π)) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hs2u : Real.sqrt 2 ≤ 1.41422 := sqrt_two_le
  have hπ : (3.14 : ℝ) ≤ π := by linarith [Real.pi_gt_d4]
  have hA81 : 81 / 100 ≤ sharpSplitRadius t - 1 / 4 := le_sharpSplitRadius_sub_quarter ht
  have hS4 : 4 ≤ Real.sqrt (t / (2 * π)) := four_le_sqrt ht
  -- abbreviations for the splitting radius, the saddle `√T` and the fractional part `p`
  set W : ℝ := sharpSplitRadius t with hWdef
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  have hW : W = (S - 1) / (2 * Real.sqrt 2) := by rw [hWdef, hSdef, sharpSplitRadius]
  have hTS : S ^ 2 = t / (2 * π) := by rw [hSdef]; exact Real.sq_sqrt hT0.le
  clear_value p S W
  have hS0 : (0 : ℝ) < S := by linarith
  have hκ : |1 / 2 - p| ≤ 1 / 2 := by
    rw [abs_le, hpdef]
    constructor <;> linarith
  -- the radius surviving the recentring of the model Gaussian
  set A : ℝ := W - 1 / 4 with hAdef
  have hA0 : (0 : ℝ) < A := by linarith
  have hAW : A + |(1 / 2 - p) / 2| ≤ W := by
    rw [hAdef, abs_div, abs_two]
    linarith
  have hbA : (1 : ℝ) ≤ 4 * π * A ^ 2 := by nlinarith
  have hSA : S ≤ 5 * A := by
    have hkey : (S + 5 / 4) * (2 * Real.sqrt 2) ≤ 5 * (S - 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hs2u hS0.le]
    have h5 : S + 5 / 4 ≤ 5 * ((S - 1) / (2 * Real.sqrt 2)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      linarith
    rw [hAdef, hW]
    linarith
  -- the Gaussian majorant: the model Gaussian against a cubic in the centred parameter
  set maj : ℝ → ℝ := fun w ↦ 11 / 5 / Real.sqrt 2 *
    (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
      (27 / 100 + 182 / 100 * |w + (1 / 2 - p) / 2|
        + 445 / 100 * (w + (1 / 2 - p) / 2) ^ 2
        + 593 / 100 * |w + (1 / 2 - p) / 2| ^ 3)) with hmajdef
  have hmajint : Integrable maj := by
    rw [hmajdef]
    exact ((integrable_exp_neg_mul_sq_mul_poly (b := 4 * π) (by positivity) _ _ _
      _).comp_add_right _).const_mul _
  clear_value maj
  -- integrability of the linear term against the model integrand
  have hFint := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  -- the pointwise majorant, valid on the whole line
  have key : ∀ w ∈ (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
      * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ ≤ maj w / S := by
    intro w _
    rw [show modelIntegrand (p : ℂ) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))
        = modelIntegrand (p : ℂ) (1 / 2) w * saddleLinear (line (1 / 2) w - (p : ℂ))
            / (S : ℂ) by ring, norm_div, Complex.norm_real, Real.norm_of_nonneg hS0.le,
      div_le_div_iff_of_pos_right hS0]
    simp only [hmajdef]
    exact norm_modelIntegrand_mul_saddleLinear_le hκ w
  -- the Gaussian tail against the cubic, at the surviving radius `A`
  have htail : ∫ w in (Set.Icc (-W) W)ᶜ, maj w
      ≤ 11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2)) := by
    simp only [hmajdef]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_compl_Icc_exp_neg_mul_sq_mul_poly_comp_add_right_le (b := 4 * π)
      (by positivity) hA0 hAW hbA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  calc ‖(1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
        * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖
      ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, ‖modelIntegrand (p : ℂ) (1 / 2) w
          * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))‖ :=
        norm_one_add_I_mul_integral_le _
    _ ≤ Real.sqrt 2 * ∫ w in (Set.Icc (-W) W)ᶜ, maj w / S :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hFint.norm.integrableOn
          (hmajint.div_const S).integrableOn measurableSet_Icc.compl key) hs2.le
    _ = Real.sqrt 2 * (∫ w in (Set.Icc (-W) W)ᶜ, maj w) / S := by
        rw [integral_div]
        ring
    _ ≤ Real.sqrt 2 * (11 / 5 / Real.sqrt 2 * (Real.exp (-(4 * π) * A ^ 2) / (4 * π)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2))) / S := by
        gcongr
    _ = 11 / (20 * π) * (S * (Real.exp (-(4 * π) * A ^ 2)
          * (27 / 100 / A + 182 / 100 + 2 * (445 / 100) * A + 2 * (593 / 100) * A ^ 2)))
            / S ^ 2 := by
        field_simp
        ring
    _ ≤ 1 / 200 / S ^ 2 := by
        gcongr
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 20 * π)]
        linarith [linear_tail_constant_le hS0.le (by linarith) hSA]
    _ = 1 / 200 / (t / (2 * π)) := by rw [hTS]

/-- The linear term over the inner region is the third derivative of the model integral
(`riemann_siegel_first.tex`, `lem:rsf_linear_tail`, second display): the truncated linear integral
differs from `-M'''(p)T^{-1/2}/(96π²)` by at most `T^{-1}/200`. -/
theorem norm_integral_linear_add_iteratedDeriv_three_modelIntegral_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {ν : ℕ} (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖(1 + I) * (∫ w in Set.Icc (-sharpSplitRadius t) (sharpSplitRadius t),
          modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
            * (saddleLinear (line (1 / 2) w - ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ))
                / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)))
        + iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2))
            ((Real.sqrt (t / (2 * π)) - ν : ℝ)) / (96 * (π : ℂ) ^ 2)
          / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)‖
      ≤ 1 / 200 / (t / (2 * π)) := by
  have hhalf : (1 / 2 : ℝ) = (0 : ℤ) + 1 / 2 := by norm_num
  set S : ℝ := Real.sqrt (t / (2 * π)) with hSdef
  set p : ℝ := S - (ν : ℝ) with hpdef
  set W : ℝ := sharpSplitRadius t with hWdef
  set F : ℝ → ℂ := fun w ↦ modelIntegrand (p : ℂ) (1 / 2) w
    * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)) with hFdef
  have hFeq : ∀ w : ℝ, F w = -(1 / 2) / (S : ℂ) * modelMomentIntegrand 1 (p : ℂ) (1 / 2) w
      + -(2 * (π : ℂ) * I / 3) / (S : ℂ) * modelMomentIntegrand 3 (p : ℂ) (1 / 2) w := fun w ↦ by
    rw [hFdef]
    simp only [modelMomentIntegrand, saddleLinear]
    ring
  have h1 := integrable_modelMomentIntegrand 1 (p : ℂ) hhalf
  have h3 := integrable_modelMomentIntegrand 3 (p : ℂ) hhalf
  have hFint : Integrable F := integrable_modelIntegrand_mul_saddleLinear_div (p : ℂ) (S : ℂ)
  -- the full-line integral is the moment identity of `lem:rsf_c1`
  have hfull : (1 + I) * ∫ w : ℝ, F w
      = -(iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2))
          / (S : ℂ) := by
    rw [funext hFeq, integral_add (h1.const_mul _) (h3.const_mul _), integral_const_mul,
      integral_const_mul,
      show (1 + I) * ((-(1 / 2) / (S : ℂ) * ∫ w : ℝ, modelMomentIntegrand 1 (p : ℂ) (1 / 2) w)
            + -(2 * (π : ℂ) * I / 3) / (S : ℂ) * ∫ w : ℝ, modelMomentIntegrand 3 (p : ℂ) (1 / 2) w)
          = (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2)
              - 2 * (π : ℂ) * I / 3 * modelMoment 3 (p : ℂ) (1 / 2)) / (S : ℂ) by
        simp only [modelMoment]; ring,
      neg_half_modelMoment_one_sub_eq (p : ℂ) hhalf]
    ring
  -- and the inner region is the whole line minus the tail
  have hsplit : (∫ w in Set.Icc (-W) W, F w) + ∫ w in (Set.Icc (-W) W)ᶜ, F w = ∫ w : ℝ, F w :=
    integral_add_compl measurableSet_Icc hFint
  have hrewrite : (1 + I) * (∫ w in Set.Icc (-W) W, F w)
      + iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
        / (S : ℂ) = -((1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, F w) := by
    rw [← hsplit] at hfull
    linear_combination hfull
  rw [hrewrite, norm_neg]
  exact norm_integral_linear_tail_le ht hν hν'

end Zeta.RiemannSiegel
