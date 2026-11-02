/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Zeta.Analysis.Complex.Exponential
public import Zeta.RiemannSiegel.Correction

/-!
# The linear Riemann–Siegel coefficient, and the explicit bounds it needs

The sharp first-order estimate of `riemann_siegel_first.tex`, `sec:rsf_sharp`, retains the next
classical coefficient `C₁(p) = −Ψ'''(p)/(96π²)` instead of bounding it away. This file defines
`C₁` through the moments `N₁` and `N₃`, which is the form in which it appears in the estimate and
which needs no differentiability of `Ψ`, and collects the four explicit numerical bounds that the
estimate consumes: on `M`, on `Ψ`, on `M'''` and on `Ψ'''`.

The bounds on `M` and on `M'''` themselves, and not only those on `Ψ` and on `C₁`, are what the
first-order formula needs: the phase swap there multiplies a *complex* modulus, and
`|Ψ| ≤ 2|M|` runs the wrong way to supply it.

All four are restricted to `p ∈ [0, 1]`, which is not cosmetic: every majorant below carries a
factor `e^{πc²}` with `c = 1/2 − p`, which is unbounded in `p`, and only `p = √T − ν ∈ [0, 1)`
is ever used.

The bound on `Ψ'''` is crude — the truth is `28.99` and this file proves `1220`. That is not slack
that sharper majorants can recover: `Ψ'''` is small by oscillatory cancellation inside
`∫ e^{2πiy²}`, which no bound passing through `‖∫ ·‖ ≤ ∫ ‖·‖` can see
(`riemann_siegel_first.tex`, `rem:rsf_psi3_refuted`).

## Main results

* `Zeta.RiemannSiegel.norm_modelIntegral_le'`, `Zeta.RiemannSiegel.abs_correction_le'`:
  `|M(p)| ≤ 11/10` and `|Ψ(p)| ≤ 11/5` on the unit interval;
* `Zeta.RiemannSiegel.norm_iteratedDeriv_three_modelIntegral_le`:
  `|M'''(p)| ≤ √2 e^{π/4}(20π + 10π² + π³)` on the unit interval, and
  `Zeta.RiemannSiegel.norm_iteratedDeriv_three_modelIntegral_le'`, its numerical form `≤ 610`;
* `Zeta.RiemannSiegel.abs_iteratedDeriv_three_correction_le`: `|Ψ'''(p)| ≤ 1220`;
* `Zeta.RiemannSiegel.correctionLinear`: the coefficient `C₁`, with
  `Zeta.RiemannSiegel.correctionLinear_eq` identifying it with `−Ψ'''/(96π²)` and
  `Zeta.RiemannSiegel.abs_correctionLinear_le` bounding it by `13/10`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- **The model integral is bounded by `11/10`** on the unit interval. -/
theorem norm_modelIntegral_le' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelIntegral (p : ℂ) (1 / 2)‖ ≤ 11 / 10 := by
  refine (norm_modelIntegral_le p).trans ?_
  have hexp : Real.exp (π * (1 / 2 - p) ^ 2) ≤ Real.exp (π / 4) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, mul_nonneg h0 (sub_nonneg.2 h1)])
  linarith [Real.exp_pi_div_four_le]

/-- **The correction function is bounded by `11/5`** on the unit interval. -/
theorem abs_correction_le' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : |correction p| ≤ 11 / 5 :=
  (abs_correction_le h0 h1).trans Real.exp_pi_div_four_le

/-- A weighted model moment is bounded by the corresponding Gaussian moments, once its weight
`‖v − p‖ ^ n` is dominated by a cubic in the centred contour parameter. -/
private theorem norm_modelMoment_le_of_norm_pow_le (n : ℕ) (p C₀ C₁ C₂ C₃ : ℝ)
    (hpt : ∀ w : ℝ, ‖line (1 / 2) w - (p : ℂ)‖ ^ n
      ≤ C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
        + C₃ * |w + (1 / 2 - p) / 2| ^ 3) :
    ‖modelMoment n (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (C₀ / 2 + C₁ / (4 * π) + C₂ / (16 * π) + C₃ / (16 * π ^ 2)) := by
  have ha : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2 := by norm_num
  have hb : (0 : ℝ) < 4 * π := by positivity
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hsqrt : Real.sqrt (π / (4 * π)) = 1 / 2 := by
    rw [show π / (4 * π) = (1 / 2 : ℝ) ^ 2 by rw [div_eq_iff (by positivity)]; ring,
      Real.sqrt_sq (by norm_num)]
  have hmajint : Integrable fun w : ℝ ↦ Real.exp (π * (1 / 2 - p) ^ 2) *
      (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
        (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
          + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) :=
    ((integrable_exp_neg_mul_sq_mul_poly hb C₀ C₁ C₂ C₃).comp_add_right
      ((1 / 2 - p) / 2)).const_mul _
  have hlhs : Integrable fun w : ℝ ↦
      Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ :=
    (integrable_modelMomentIntegrand n (p : ℂ) ha).norm.const_mul _
  have hstep : ∀ w : ℝ, Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
          (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
            + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) := by
    intro w
    calc Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖
        = ‖line (1 / 2) w - (p : ℂ)‖ ^ n *
            (Real.sqrt 2 * ‖modelIntegrand (p : ℂ) (1 / 2) w‖) := by
          rw [modelMomentIntegrand, norm_mul, norm_pow]; ring
      _ ≤ ‖line (1 / 2) w - (p : ℂ)‖ ^ n *
            ‖exp (2 * π * I * (line (1 / 2) w - (p : ℂ)) ^ 2)‖ := by
          gcongr
          exact (le_div_iff₀' (Real.sqrt_pos.2 two_pos)).mp (norm_modelIntegrand_le (p : ℂ) ha w)
      _ ≤ (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
            + C₃ * |w + (1 / 2 - p) / 2| ^ 3) *
            (Real.exp (π * (1 / 2 - p) ^ 2) *
              Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2)) := by
          rw [norm_exp_two_pi_mul_I_mul_line_sub_sq]
          gcongr
          exact hpt w
      _ = _ := by ring
  calc ‖modelMoment n (p : ℂ) (1 / 2)‖
      ≤ Real.sqrt 2 * ∫ w : ℝ, ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ := by
        rw [modelMoment]; exact norm_one_add_I_mul_integral_le _
    _ = ∫ w : ℝ, Real.sqrt 2 * ‖modelMomentIntegrand n (p : ℂ) (1 / 2) w‖ :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ w : ℝ, Real.exp (π * (1 / 2 - p) ^ 2) *
          (Real.exp (-(4 * π) * (w + (1 / 2 - p) / 2) ^ 2) *
            (C₀ + C₁ * |w + (1 / 2 - p) / 2| + C₂ * (w + (1 / 2 - p) / 2) ^ 2
              + C₃ * |w + (1 / 2 - p) / 2| ^ 3)) := integral_mono hlhs hmajint hstep
    _ = Real.exp (π * (1 / 2 - p) ^ 2) * ∫ u : ℝ, Real.exp (-(4 * π) * u ^ 2) *
          (C₀ + C₁ * |u| + C₂ * u ^ 2 + C₃ * |u| ^ 3) := by
        rw [integral_const_mul]
        exact congrArg _ (integral_add_right_eq_self (fun u : ℝ ↦ Real.exp (-(4 * π) * u ^ 2) *
          (C₀ + C₁ * |u| + C₂ * u ^ 2 + C₃ * |u| ^ 3)) ((1 / 2 - p) / 2))
    _ = _ := by
        rw [integral_exp_neg_mul_sq_mul_poly hb, hsqrt]
        field_simp
        ring

/-- **A Gaussian bound for the first moment `N₁`** on the unit interval. -/
private theorem norm_modelMoment_one_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelMoment 1 (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (1 / 8 + 1 / (4 * π))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine (norm_modelMoment_le_of_norm_pow_le 1 p (Real.sqrt 2 / 4) (Real.sqrt 2) 0 0
    fun w ↦ ?_).trans_eq ?_
  · have hc : |1 / 2 - p| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hle := norm_line_sub_ofReal_le' (1 / 2) w p
    rw [pow_one]
    nlinarith [Real.sqrt_nonneg 2, abs_nonneg (w + (1 / 2 - p) / 2)]
  · field_simp
    ring

/-- **A Gaussian bound for the third moment `N₃`** on the unit interval. -/
private theorem norm_modelMoment_three_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖modelMoment 3 (p : ℂ) (1 / 2)‖
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) *
        (Real.sqrt 2 * (1 / 64 + 1 / (16 * π) + 1 / (8 * π ^ 2))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  refine (norm_modelMoment_le_of_norm_pow_le 3 p (Real.sqrt 2 / 32) (Real.sqrt 2 / 8)
    (Real.sqrt 2 / 2) (2 * Real.sqrt 2) fun w ↦ ?_).trans_eq ?_
  · set X := |w + (1 / 2 - p) / 2| with hX
    have hXsq : X ^ 2 = (w + (1 / 2 - p) / 2) ^ 2 := by rw [hX]; exact sq_abs _
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hc : |1 / 2 - p| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hc2 : (1 / 2 - p) ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg (1 / 2 - p), sq_abs (1 / 2 - p)]
    have hY0 : (0 : ℝ) ≤ ‖line (1 / 2) w - (p : ℂ)‖ := norm_nonneg _
    have hYsq : ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 = 2 * X ^ 2 + (1 / 2 - p) ^ 2 / 2 := by
      rw [norm_line_sub_ofReal_sq, hXsq]
    have hYle : ‖line (1 / 2) w - (p : ℂ)‖ ≤ Real.sqrt 2 * (X + 1 / 4) := by
      have hle := norm_line_sub_ofReal_le' (1 / 2) w p
      nlinarith
    calc ‖line (1 / 2) w - (p : ℂ)‖ ^ 3
        = ‖line (1 / 2) w - (p : ℂ)‖ ^ 2 * ‖line (1 / 2) w - (p : ℂ)‖ := by ring
      _ ≤ (2 * X ^ 2 + 1 / 8) * (Real.sqrt 2 * (X + 1 / 4)) := by
          rw [hYsq]
          exact mul_le_mul (by linarith) hYle hY0 (by positivity)
      _ = Real.sqrt 2 / 32 + Real.sqrt 2 / 8 * X + Real.sqrt 2 / 2 * X ^ 2
            + 2 * Real.sqrt 2 * X ^ 3 := by ring
      _ = _ := by rw [← hXsq]
  · field_simp
    ring

/-- **The third derivative of the model integral is bounded** on the unit interval
(`riemann_siegel_first.tex`, `lem:rsf_psi3`). -/
theorem norm_iteratedDeriv_three_modelIntegral_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖
      ≤ Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ' : π ≠ 0 := hπ.ne'
  have hexp : Real.exp (π * (1 / 2 - p) ^ 2) ≤ Real.exp (π / 4) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)])
  rw [iteratedDeriv_three_modelIntegral (p : ℂ) (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hπ, Complex.norm_I, mul_one]
  calc 48 * π ^ 2 * ‖modelMoment 1 (p : ℂ) (1 / 2)‖
        + 64 * π ^ 3 * ‖modelMoment 3 (p : ℂ) (1 / 2)‖
      ≤ 48 * π ^ 2 * (Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (1 / 8 + 1 / (4 * π))))
          + 64 * π ^ 3 * (Real.exp (π * (1 / 2 - p) ^ 2) *
            (Real.sqrt 2 * (1 / 64 + 1 / (16 * π) + 1 / (8 * π ^ 2)))) :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_modelMoment_one_le h0 h1) (by positivity))
          (mul_le_mul_of_nonneg_left (norm_modelMoment_three_le h0 h1) (by positivity))
    _ = Real.exp (π * (1 / 2 - p) ^ 2) * (Real.sqrt 2 * (20 * π + 10 * π ^ 2 + π ^ 3)) := by
        field_simp
        ring
    _ ≤ Real.exp (π / 4) * (Real.sqrt 2 * (20 * π + 10 * π ^ 2 + π ^ 3)) := by
        gcongr
    _ = Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3) := by ring

/-- **The third derivative of the model integral is bounded by `610`** on the unit interval. -/
theorem norm_iteratedDeriv_three_modelIntegral_le' {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ ≤ 610 := by
  refine (norm_iteratedDeriv_three_modelIntegral_le h0 h1).trans ?_
  have hs2 : Real.sqrt 2 ≤ 1.415 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hK : 20 * π + 10 * π ^ 2 + π ^ 3 ≤ 193 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  calc Real.sqrt 2 * Real.exp (π / 4) * (20 * π + 10 * π ^ 2 + π ^ 3)
      ≤ 1.415 * (11 / 5) * 193 :=
        mul_le_mul (mul_le_mul hs2 Real.exp_pi_div_four_le (Real.exp_pos _).le (by norm_num)) hK
          (by positivity) (by norm_num)
    _ ≤ 610 := by norm_num

/-- **The third derivative of the correction function is bounded by `1220`** on the unit interval
(`riemann_siegel_first.tex`, `lem:rsf_psi3`). -/
theorem abs_iteratedDeriv_three_correction_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    |iteratedDeriv 3 correction p| ≤ 1220 := by
  have hunit : ‖exp (-((π / 8 : ℝ) * I))‖ = 1 := by simp [Complex.norm_exp]
  rw [iteratedDeriv_three_correction p, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |(exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)).re|
      ≤ 2 * ‖exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ := by
        gcongr
        exact Complex.abs_re_le_norm _
    _ = 2 * ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖ := by
        rw [norm_mul, hunit, one_mul]
    _ ≤ 2 * 610 := by
        gcongr
        exact norm_iteratedDeriv_three_modelIntegral_le' h0 h1
    _ = 1220 := by norm_num

/-- **The linear coefficient is the classical one**: `C₁(p) = −Ψ'''(p)/(96π²)`. -/
theorem correctionLinear_eq (p : ℝ) :
    correctionLinear p = -iteratedDeriv 3 correction p / (96 * π ^ 2) :=
  (neg_iteratedDeriv_three_correction_div_eq p).symm

/-- **The linear coefficient is bounded by `13/10`** on the unit interval. -/
theorem abs_correctionLinear_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    |correctionLinear p| ≤ 13 / 10 := by
  have hpos : (0 : ℝ) < 96 * π ^ 2 := by positivity
  rw [correctionLinear_eq, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith [abs_iteratedDeriv_three_correction_le h0 h1, Real.pi_gt_d2, Real.pi_pos]

end Zeta.RiemannSiegel
