/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Zeta.Analysis.Calculus.IteratedDeriv
public import Zeta.Analysis.SpecialFunctions.Gaussian
public import Zeta.RiemannSiegel.Model

/-!
# The weighted moments of the Riemann–Siegel model integral

The sharp first-order estimate replaces the crude bound `|e^Δ − 1| ≤ …` of
`Zeta.RiemannSiegel.norm_integral_inner_le` by an exact evaluation of the `ζ`-linear part of
`e^Δ − 1`, whose coefficients are the **weighted model moments**

`N_n(p) = ∫_{L(1/2)} (v − p)^n e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`

(`riemann_siegel_first.tex`, `def:rsf_moment`), of which `N_0` is the model integral
`Zeta.RiemannSiegel.modelIntegral` itself.

The estimates of this file are stated uniformly in the centre `p`, through an upper bound `P` for
`‖p‖`: the majorant is then independent of `p` on any ball, which is what differentiation under
the integral sign in `p` needs.

## Main results

* `Zeta.RiemannSiegel.modelMomentIntegrand`, `Zeta.RiemannSiegel.modelMoment`: the weighted
  integrand along `L(a)` and its integral `N_n(p)`;
* `Zeta.RiemannSiegel.modelMoment_zero`: `N_0 = M`;
* `Zeta.RiemannSiegel.norm_modelMomentIntegrand_le`: a Gaussian majorant depending on `p` only
  through a bound `‖p‖ ≤ P`;
* `Zeta.RiemannSiegel.integrable_modelMomentIntegrand`: absolute convergence, for every complex
  `p` and every order `n`;
* `Zeta.RiemannSiegel.hasDerivAt_modelMoment`: the recursion `N_n' = −n N_{n−1} − 4πi N_{n+1}`;
* `Zeta.RiemannSiegel.iteratedDeriv_three_modelIntegral`: `M''' = 48π² N₁ + 64π³ i N₃`;
* `Zeta.RiemannSiegel.neg_half_modelMoment_one_sub_eq`: `−N₁/2 − (2πi/3) N₃ = −M'''/(96π²)`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **integrand of the weighted Riemann–Siegel model moment** along the contour `L(a)`: the
model integrand `Zeta.RiemannSiegel.modelIntegrand` weighted by `(v − p)^n`. -/
noncomputable def modelMomentIntegrand (n : ℕ) (p : ℂ) (a w : ℝ) : ℂ :=
  (line a w - p) ^ n * modelIntegrand p a w

/-- The **weighted Riemann–Siegel model moment**
`N_n(p) = ∫_{L(1/2)} (v − p)^n e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`, taken here along the
contour `L(a)`, whose constant velocity is `1 + i`. -/
noncomputable def modelMoment (n : ℕ) (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelMomentIntegrand n p a w

/-- **The zeroth moment is the model integral.** -/
theorem modelMoment_zero (p : ℂ) (a : ℝ) : modelMoment 0 p a = modelIntegral p a := by
  simp only [modelMoment, modelMomentIntegrand, modelIntegral, pow_zero, one_mul]

/-- **The weighted model integrand is continuous along a half-integer contour.** -/
theorem continuous_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Continuous (modelMomentIntegrand n p a) :=
  (((continuous_line a).sub continuous_const).pow n).mul (continuous_modelIntegrand p ha)

/-- **A Gaussian majorant for the weighted model integrand**, depending on the centre `p` only
through an upper bound `P` for `‖p‖`. -/
theorem norm_modelMomentIntegrand_le (n : ℕ) {p : ℂ} {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2)
    {P : ℝ} (hP : ‖p‖ ≤ P) (w : ℝ) :
    ‖modelMomentIntegrand n p a w‖
      ≤ Real.exp (4 * π * P * (|a| + P)) / Real.sqrt 2 *
        ((|a| + P + Real.sqrt 2 * |w|) ^ n *
          Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|)) := by
  have hP0 : 0 ≤ P := (norm_nonneg p).trans hP
  have hre := abs_le.mp ((Complex.abs_re_le_norm p).trans hP)
  have him := abs_le.mp ((Complex.abs_im_le_norm p).trans hP)
  have h1 : ‖line a w - p‖ ≤ |a| + P + Real.sqrt 2 * |w| := by
    calc ‖line a w - p‖ ≤ ‖line a w‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ |a| + Real.sqrt 2 * |w| + P := by gcongr; simpa using norm_line_sub_ofReal_le a w 0
      _ = |a| + P + Real.sqrt 2 * |w| := by ring
  have h2 : ‖exp (2 * π * I * (line a w - p) ^ 2)‖
      ≤ Real.exp (4 * π * P * (|a| + P)) *
        Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|) := by
    rw [Complex.norm_exp_two_pi_mul_I_mul_sq, ← Real.exp_add, Complex.sub_re, Complex.sub_im,
      line_re, line_im]
    refine Real.exp_le_exp.2 ?_
    have hw1 : -(w * (a - p.re - p.im)) ≤ (|a| + 2 * P) * |w| :=
      (neg_le_abs _).trans <| by
        rw [abs_mul, mul_comm (|a| + 2 * P) |w|]
        gcongr
        exact abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
    have hw2 : p.im * (a - p.re) ≤ P * (|a| + P) :=
      (le_abs_self _).trans <| by
        rw [abs_mul]
        exact mul_le_mul ((Complex.abs_im_le_norm p).trans hP)
          (abs_le.2 ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩) (abs_nonneg _) hP0
    have key : -((a + w - p.re) * (w - p.im))
        ≤ -w ^ 2 + (|a| + 2 * P) * |w| + P * (|a| + P) := by linarith
    linarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 4 * π)]
  calc ‖modelMomentIntegrand n p a w‖ = ‖line a w - p‖ ^ n * ‖modelIntegrand p a w‖ := by
        rw [modelMomentIntegrand, norm_mul, norm_pow]
    _ ≤ (|a| + P + Real.sqrt 2 * |w|) ^ n *
          (Real.exp (4 * π * P * (|a| + P)) *
            Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|) / Real.sqrt 2) := by
        gcongr
        exact (norm_modelIntegrand_le p ha w).trans (by gcongr)
    _ = Real.exp (4 * π * P * (|a| + P)) / Real.sqrt 2 *
          ((|a| + P + Real.sqrt 2 * |w|) ^ n *
            Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * P) * |w|)) := by ring

/-- **Absolute convergence of the weighted model moment**, for every complex `p` and every
order `n`. -/
theorem integrable_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Integrable (modelMomentIntegrand n p a) := by
  have hmaj : Integrable fun w : ℝ ↦ Real.exp (4 * π * ‖p‖ * (|a| + ‖p‖)) / Real.sqrt 2 *
      ((|a| + ‖p‖ + Real.sqrt 2 * |w|) ^ n *
        Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * ‖p‖) * |w|)) :=
    (integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (b := 4 * π) (by positivity)
      (by positivity) (Real.sqrt_nonneg 2) _ n).const_mul _
  exact hmaj.mono' (continuous_modelMomentIntegrand n p ha).aestronglyMeasurable
    (.of_forall fun w ↦ norm_modelMomentIntegrand_le n ha le_rfl w)

/-- **The derivative of the weighted model integrand in its centre `p`**, in terms of the
neighbouring integrands. -/
theorem hasDerivAt_modelMomentIntegrand (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2)
    (w : ℝ) :
    HasDerivAt (fun q : ℂ ↦ modelMomentIntegrand n q a w)
      (-(n : ℂ) * modelMomentIntegrand (n - 1) p a w
        - 4 * π * I * modelMomentIntegrand (n + 1) p a w) p := by
  -- at `n = 0` the term with the truncated subtraction `n − 1` carries the factor `n = 0`
  have hD : (2 : ℂ) * I * sin (π * line a w) ≠ 0 := by
    simpa [I_ne_zero] using sin_pi_mul_line_ne_zero ha w
  have hfun : ∀ (k : ℕ) (q : ℂ), modelMomentIntegrand k q a w
      = (line a w - q) ^ k * exp (2 * π * I * (line a w - q) ^ 2) /
          (2 * I * sin (π * line a w)) := fun k q ↦ by
    rw [modelMomentIntegrand, modelIntegrand, modelFun_eq_div_two_mul_I_mul_sin]
    ring
  have hg : HasDerivAt (fun q : ℂ ↦ line a w - q) (-1) p := by
    simpa using (hasDerivAt_id p).const_sub (line a w)
  have hpow : HasDerivAt (fun q : ℂ ↦ (line a w - q) ^ n)
      (-(n : ℂ) * (line a w - p) ^ (n - 1)) p := (hg.pow n).congr_deriv (by ring)
  -- the step is type-ascribed, so that the beta-redexes the derivative rules leave behind are
  -- discharged by defeq
  have hquad : HasDerivAt (fun q : ℂ ↦ 2 * (π : ℂ) * I * (line a w - q) ^ 2)
      (-(4 * (π : ℂ) * I) * (line a w - p)) p :=
    ((hg.pow 2).const_mul (2 * (π : ℂ) * I)).congr_deriv (by push_cast; ring)
  simp only [hfun]
  refine ((hpow.mul hquad.cexp).div_const (2 * I * sin (π * line a w))).congr_deriv ?_
  field_simp
  ring

/-- **The derivative of the weighted model moment in its centre `p`**:
`N_n' = −n N_{n−1} − 4πi N_{n+1}`. -/
theorem hasDerivAt_modelMoment (n : ℕ) (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    HasDerivAt (fun q : ℂ ↦ modelMoment n q a)
      (-(n : ℂ) * modelMoment (n - 1) p a - 4 * π * I * modelMoment (n + 1) p a) p := by
  -- differentiation under the integral sign, against a majorant valid on the whole unit ball
  -- about `p` and integrable at every order
  obtain ⟨maj, hmajint, hmajle⟩ : ∃ maj : ℕ → ℝ → ℝ, (∀ k, Integrable (maj k)) ∧
      ∀ (k : ℕ) (q : ℂ), ‖q‖ ≤ ‖p‖ + 1 → ∀ w : ℝ, ‖modelMomentIntegrand k q a w‖ ≤ maj k w :=
    ⟨fun k w ↦ Real.exp (4 * π * (‖p‖ + 1) * (|a| + (‖p‖ + 1))) / Real.sqrt 2 *
        ((|a| + (‖p‖ + 1) + Real.sqrt 2 * |w|) ^ k *
          Real.exp (-(4 * π) * w ^ 2 + 4 * π * (|a| + 2 * (‖p‖ + 1)) * |w|)),
      fun k ↦ (integrable_pow_add_mul_abs_mul_exp_neg_mul_sq_add_mul_abs (b := 4 * π)
        (A := |a| + (‖p‖ + 1)) (β := Real.sqrt 2) (by positivity) (by positivity)
        (Real.sqrt_nonneg 2) _ k).const_mul _,
      fun k q hq w ↦ norm_modelMomentIntegrand_le k ha hq w⟩
  have hcoeff : ‖4 * (π : ℂ) * I‖ = 4 * π := by
    simp [abs_of_pos Real.pi_pos]
  have hbound : ∀ w : ℝ, ∀ q ∈ Metric.ball p 1,
      ‖-(n : ℂ) * modelMomentIntegrand (n - 1) q a w
        - 4 * π * I * modelMomentIntegrand (n + 1) q a w‖
        ≤ (n : ℝ) * maj (n - 1) w + 4 * π * maj (n + 1) w := by
    intro w q hq
    rw [Metric.mem_ball, dist_eq_norm] at hq
    have hqP : ‖q‖ ≤ ‖p‖ + 1 := by linarith [norm_le_insert' q p]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_natCast, norm_mul, hcoeff]
    gcongr <;> exact hmajle _ q hqP w
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := p)
    (F := fun (q : ℂ) (w : ℝ) ↦ modelMomentIntegrand n q a w)
    (F' := fun (q : ℂ) (w : ℝ) ↦ -(n : ℂ) * modelMomentIntegrand (n - 1) q a w
      - 4 * π * I * modelMomentIntegrand (n + 1) q a w)
    (bound := fun w ↦ (n : ℝ) * maj (n - 1) w + 4 * π * maj (n + 1) w)
    (s := Metric.ball p 1) (Metric.ball_mem_nhds p one_pos)
    (Filter.Eventually.of_forall fun q ↦
      (continuous_modelMomentIntegrand n q ha).aestronglyMeasurable)
    (integrable_modelMomentIntegrand n p ha)
    (((continuous_const.mul (continuous_modelMomentIntegrand (n - 1) p ha)).sub
      (continuous_const.mul (continuous_modelMomentIntegrand (n + 1) p ha))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (((hmajint _).const_mul _).add ((hmajint _).const_mul _))
    (Filter.Eventually.of_forall fun w q _ ↦ hasDerivAt_modelMomentIntegrand n q ha w)
  have hsplit : ∫ w : ℝ, (-(n : ℂ) * modelMomentIntegrand (n - 1) p a w
      - 4 * π * I * modelMomentIntegrand (n + 1) p a w)
      = -(n : ℂ) * (∫ w : ℝ, modelMomentIntegrand (n - 1) p a w)
        - 4 * π * I * ∫ w : ℝ, modelMomentIntegrand (n + 1) p a w := by
    rw [integral_sub ((integrable_modelMomentIntegrand _ p ha).const_mul _)
      ((integrable_modelMomentIntegrand _ p ha).const_mul _), integral_const_mul,
      integral_const_mul]
  simp only [modelMoment]
  exact ((hkey.2.congr_deriv hsplit).const_mul (1 + I)).congr_deriv (by ring)

/-- **The weighted model moments are entire in their centre.** -/
theorem differentiable_modelMoment (n : ℕ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    Differentiable ℂ fun q : ℂ ↦ modelMoment n q a :=
  fun p ↦ (hasDerivAt_modelMoment n p ha).differentiableAt

/-- **The derivative of the model integral in its centre**: `M' = −4πi N₁`. -/
theorem hasDerivAt_modelIntegral (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    HasDerivAt (fun q : ℂ ↦ modelIntegral q a) (-(4 * π * I) * modelMoment 1 p a) p := by
  have h := hasDerivAt_modelMoment 0 p ha
  simp only [modelMoment_zero] at h
  exact h.congr_deriv (by push_cast; ring)

/-- **The third derivative of the model integral in its centre**
(`riemann_siegel_first.tex`, `lem:rsf_moment_deriv`): `M''' = 48π² N₁ + 64π³ i N₃`. -/
theorem iteratedDeriv_three_modelIntegral (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a) p
      = 48 * π ^ 2 * modelMoment 1 p a + 64 * π ^ 3 * I * modelMoment 3 p a := by
  have e₁ : iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a)
      = iteratedDeriv 2 fun q : ℂ ↦ -(4 * π * I) * modelMoment 1 q a :=
    iteratedDeriv_succ_of_hasDerivAt (fun q ↦ hasDerivAt_modelIntegral q ha) 2
  have e₂ : (iteratedDeriv 2 fun q : ℂ ↦ -(4 * π * I) * modelMoment 1 q a)
      = iteratedDeriv 1 fun q : ℂ ↦
          4 * π * I * modelIntegral q a - 16 * π ^ 2 * modelMoment 2 q a := by
    refine iteratedDeriv_succ_of_hasDerivAt (fun q ↦ ?_) 1
    refine ((hasDerivAt_modelMoment 1 q ha).const_mul (-(4 * (π : ℂ) * I))).congr_deriv ?_
    simp only [Nat.sub_self, modelMoment_zero]
    push_cast
    linear_combination (16 * (π : ℂ) ^ 2 * modelMoment 2 q a) * Complex.I_sq
  have e₃ : (iteratedDeriv 1 fun q : ℂ ↦
        4 * π * I * modelIntegral q a - 16 * π ^ 2 * modelMoment 2 q a)
      = iteratedDeriv 0 fun q : ℂ ↦
          48 * π ^ 2 * modelMoment 1 q a + 64 * π ^ 3 * I * modelMoment 3 q a := by
    refine iteratedDeriv_succ_of_hasDerivAt (fun q ↦ ?_) 0
    refine (((hasDerivAt_modelIntegral q ha).const_mul (4 * (π : ℂ) * I)).sub
      ((hasDerivAt_modelMoment 2 q ha).const_mul (16 * (π : ℂ) ^ 2))).congr_deriv ?_
    push_cast
    linear_combination (-(16 * (π : ℂ) ^ 2 * modelMoment 1 q a)) * Complex.I_sq
  rw [e₁, e₂, e₃, iteratedDeriv_zero]

/-- **The linear coefficient of the sharp first-order estimate is a third derivative**
(`riemann_siegel_first.tex`, `lem:rsf_c1`):
`−N₁/2 − (2πi/3) N₃ = −M'''/(96π²)`. -/
theorem neg_half_modelMoment_one_sub_eq (p : ℂ) {a : ℝ} {m : ℤ} (ha : a = m + 1 / 2) :
    -(1 / 2) * modelMoment 1 p a - 2 * π * I / 3 * modelMoment 3 p a
      = -iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q a) p / (96 * π ^ 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [iteratedDeriv_three_modelIntegral p ha]
  field_simp
  ring

end Zeta.RiemannSiegel
