/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Zeta.RiemannSiegel.Integral

/-!
# The Hankel ray integral

The contour `Zeta.RiemannSiegel.line` through the *origin* is the diagonal
`L(0)(w) = √2 w e^{iπ/4}`, whose two halves are the Hankel rays `ρ e^{iπ/4}` and `ρ e^{-3iπ/4}`.
Along them the Riemann–Siegel integrand collapses to a single integral over the positive reals
(`riemann_siegel_zero.tex`, `lem:rsz_hankel`): `I(s, 0) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`, where
`Φ(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4}) dρ`.

The hypothesis `Re s < 0` is exactly what makes `Φ` converge: the kernel has a simple pole at the
origin, so the integrand is `O(ρ^{-Re s - 1})` there. It is therefore also the hypothesis under
which `L(0)` may be used at all, passing as it does straight through that pole (the contours of
`Zeta/RiemannSiegel/Shift.lean` all pass beside it).

What is proved here concerns `I(s, 0)`; identifying it with `I(s, ½)` is separate.

## Main results

* `Zeta.RiemannSiegel.hankelIntegrand`, `Zeta.RiemannSiegel.hankelIntegral`: the integrand of `Φ`
  and `Φ` itself;
* `Zeta.RiemannSiegel.norm_hankelIntegrand_le`: the bound `O(ρ^{-Re s - 1} e^{-πρ²})`;
* `Zeta.RiemannSiegel.integrableOn_hankelIntegrand`: absolute convergence of `Φ(s)` for
  `Re s < 0`;
* `Zeta.RiemannSiegel.exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq`: the Gaussian factor
  of the kernel is real on the ray;
* `Zeta.RiemannSiegel.integrand_ofReal_mul_exp_pi_div_four_mul_I`,
  `Zeta.RiemannSiegel.integrand_neg_ofReal_mul_exp_pi_div_four_mul_I`: the integrand on the two
  rays;
* `Zeta.RiemannSiegel.integrable_contourIntegrand_zero`: absolute integrability along `L(0)`;
* `Zeta.RiemannSiegel.contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral`:
  `I(s, 0) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The Hankel ray integrand `ρ ↦ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4})`, the restriction of the
Riemann–Siegel integrand to the diagonal ray with the constant phases stripped off. -/
noncomputable def hankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp ((π / 4 : ℝ) * I))

/-- The Hankel ray integral `Φ(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4}) dρ`. The
integrand is integrable only for `Re s < 0` (`integrableOn_hankelIntegrand`); elsewhere the value
is the junk value `0`. -/
noncomputable def hankelIntegral (s : ℂ) : ℂ :=
  ∫ ρ in Set.Ioi (0 : ℝ), hankelIntegrand s ρ

/-! ### Convergence -/

/-- Linear lower bound for the kernel denominator along the diagonal ray. -/
theorem norm_sin_pi_mul_ray_ge' {ρ : ℝ} (hρ : 0 ≤ ρ) :
    π * ρ / Real.sqrt 2 ≤ ‖sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))‖ := by
  have h := sinh_le_norm_sin_pi_mul_line 0 (ρ / Real.sqrt 2)
  rw [line_zero, show (Real.sqrt 2 * (ρ / Real.sqrt 2) : ℝ) = ρ by
      field_simp, ← mul_assoc, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ / Real.sqrt 2),
    ← mul_div_assoc] at h
  exact (Real.self_le_sinh_iff.2 (by positivity)).trans h

/-- The Hankel ray integrand is continuous away from the origin. -/
theorem continuousOn_hankelIntegrand (s : ℂ) :
    ContinuousOn (hankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  have hsin : ∀ ρ ∈ Set.Ioi (0 : ℝ), sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I)) ≠ 0 :=
    fun ρ (hρ : (0 : ℝ) < ρ) ↦
      norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (norm_sin_pi_mul_ray_ge' hρ.le))
  refine ContinuousOn.div (ContinuousOn.mul ?_ (by fun_prop)) (by fun_prop) hsin
  exact ContinuousOn.cpow (by fun_prop) continuousOn_const fun ρ hρ ↦
    mem_slitPlane_iff.2 (Or.inl (by simpa using hρ))

/-- The Hankel ray integrand is `O(ρ^{-Re s - 1} e^{-πρ²})`. -/
theorem norm_hankelIntegrand_le (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖hankelIntegrand s ρ‖ ≤ Real.sqrt 2 / π * (ρ ^ (-s.re - 1) * Real.exp (-π * ρ ^ 2)) := by
  have hden := norm_sin_pi_mul_ray_ge' hρ.le
  rw [hankelIntegrand, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hρ,
    show (-((π : ℂ) * (ρ : ℂ) ^ 2)) = (((-π * ρ ^ 2 : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_exp, Complex.ofReal_re, Complex.neg_re]
  calc ρ ^ (-s.re) * Real.exp (-π * ρ ^ 2) / ‖sin ((π : ℂ) * ρ * exp ((π / 4 : ℝ) * I))‖
      ≤ ρ ^ (-s.re) * Real.exp (-π * ρ ^ 2) / (π * ρ / Real.sqrt 2) := by gcongr
    _ = Real.sqrt 2 / π * (ρ ^ (-s.re - 1) * Real.exp (-π * ρ ^ 2)) := by
        rw [Real.rpow_sub hρ, Real.rpow_one]
        field_simp

/-- Absolute convergence of the Hankel ray integral `Φ(s)`, for `Re s < 0`. -/
theorem integrableOn_hankelIntegrand {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (hankelIntegrand s) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos
      (by linarith : (-1 : ℝ) < -s.re - 1)).const_mul (Real.sqrt 2 / π))
    ((continuousOn_hankelIntegrand s).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ using norm_hankelIntegrand_le s hρ

/-! ### The integrand on the two rays -/

/-- On the diagonal ray the Gaussian factor of the kernel is real: `e^{iπx²} = e^{-πρ²}` at
`x = ρ e^{iπ/4}`. -/
theorem exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq (ρ : ℝ) :
    exp ((π : ℂ) * I * ((ρ : ℂ) * exp ((π / 4 : ℝ) * I)) ^ 2) = exp (-(π * (ρ : ℂ) ^ 2)) := by
  congr 1
  linear_combination ((π : ℂ) * I * (ρ : ℂ) ^ 2) * Complex.exp_pi_div_four_mul_I_mul_self
    + ((π : ℂ) * (ρ : ℂ) ^ 2) * Complex.I_sq

/-- The Riemann–Siegel integrand on the outgoing Hankel ray `ρ e^{iπ/4}`. -/
theorem integrand_ofReal_mul_exp_pi_div_four_mul_I (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    integrand s ((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) * hankelIntegrand s ρ := by
  rw [integrand, kernel_eq_div_two_mul_I_mul_sin,
    slantCpow_ofReal_mul_exp_pi_div_four_mul_I hρ (-s),
    exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq,
    show ((π / 4 : ℝ) : ℂ) * I * (-s) = ((-(π / 4) : ℝ) : ℂ) * I * s by push_cast; ring,
    hankelIntegrand, mul_assoc ((π : ℂ)) ((ρ : ℂ))]
  field_simp

/-- The Riemann–Siegel integrand on the incoming Hankel ray `ρ e^{-3iπ/4}`. -/
theorem integrand_neg_ofReal_mul_exp_pi_div_four_mul_I (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    integrand s (-((ρ : ℂ) * exp ((π / 4 : ℝ) * I)))
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) * hankelIntegrand s ρ := by
  rw [integrand, slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I hρ (-s),
    show ((-(3 * π / 4) : ℝ) : ℂ) * I * (-s) = ((3 * π / 4 : ℝ) : ℂ) * I * s by push_cast; ring,
    kernel_neg, kernel_eq_div_two_mul_I_mul_sin,
    exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq, hankelIntegrand,
    mul_assoc ((π : ℂ)) ((ρ : ℂ))]
  field_simp

/-! ### The contour through the origin -/

/-- The Riemann–Siegel contour integrand along `L(0)`, on the outgoing ray. -/
theorem contourIntegrand_zero_of_pos (s : ℂ) {w : ℝ} (hw : 0 < w) :
    contourIntegrand s 0 w
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) * hankelIntegrand s (Real.sqrt 2 * w) := by
  rw [contourIntegrand, line_zero]
  exact integrand_ofReal_mul_exp_pi_div_four_mul_I s (mul_pos (Real.sqrt_pos.2 two_pos) hw)

/-- The Riemann–Siegel contour integrand along `L(0)`, on the incoming ray. -/
theorem contourIntegrand_zero_of_neg (s : ℂ) {w : ℝ} (hw : w < 0) :
    contourIntegrand s 0 w
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) * hankelIntegrand s (Real.sqrt 2 * -w) := by
  rw [contourIntegrand, line_zero,
    show ((Real.sqrt 2 * w : ℝ) : ℂ) = -(((Real.sqrt 2 * -w : ℝ)) : ℂ) by push_cast; ring, neg_mul]
  exact integrand_neg_ofReal_mul_exp_pi_div_four_mul_I s
    (mul_pos (Real.sqrt_pos.2 two_pos) (neg_pos.2 hw))

/-- Absolute convergence of the Hankel ray integral in the parametrisation by `L(0)`, in which
the ray is traversed at speed `√2`. -/
theorem integrableOn_hankelIntegrand_comp_mul_left {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (fun w : ℝ ↦ hankelIntegrand s (Real.sqrt 2 * w)) (Set.Ioi (0 : ℝ)) :=
  (integrableOn_Ioi_comp_mul_left_iff (hankelIntegrand s) 0 (Real.sqrt_pos.2 two_pos)).2
    (by simpa using integrableOn_hankelIntegrand hs)

/-- The contour through the origin is integrable on the outgoing ray. -/
theorem integrableOn_contourIntegrand_zero_Ioi {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (contourIntegrand s 0) (Set.Ioi (0 : ℝ)) :=
  IntegrableOn.congr_fun ((integrableOn_hankelIntegrand_comp_mul_left hs).const_mul _)
    (fun _ hw ↦ (contourIntegrand_zero_of_pos s hw).symm) measurableSet_Ioi

/-- The contour through the origin is integrable on the incoming ray. -/
theorem integrableOn_contourIntegrand_zero_Iic {s : ℂ} (hs : s.re < 0) :
    IntegrableOn (contourIntegrand s 0) (Set.Iic (0 : ℝ)) := by
  have hneg : IntegrableOn (fun w : ℝ ↦ hankelIntegrand s (Real.sqrt 2 * -w))
      (Set.Iio (0 : ℝ)) := by
    simpa using (integrableOn_hankelIntegrand_comp_mul_left hs).comp_neg
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  exact IntegrableOn.congr_fun (hneg.const_mul _)
    (fun w hw ↦ (contourIntegrand_zero_of_neg s hw).symm) measurableSet_Iio

/-- The Riemann–Siegel contour integrand is absolutely integrable along `L(0)`. -/
theorem integrable_contourIntegrand_zero {s : ℂ} (hs : s.re < 0) :
    Integrable (contourIntegrand s 0) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨integrableOn_contourIntegrand_zero_Iic hs, integrableOn_contourIntegrand_zero_Ioi hs⟩

/-- The Hankel-ray representation of the Riemann–Siegel contour integral through the origin
(`riemann_siegel_zero.tex`, `lem:rsz_hankel`): for `Re s < 0`,
`I(s, 0) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`. -/
theorem contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral {s : ℂ} (hs : s.re < 0) :
    contourIntegral s 0
      = -(exp ((π / 4 : ℝ) * I * (1 + s)) * sin ((π : ℂ) * s / 2)) * hankelIntegral s := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs2.ne'
  -- each ray is a rescaling of `Φ`
  have hscale : ∀ c : ℂ, (∫ w in Set.Ioi (0 : ℝ), c * hankelIntegrand s (Real.sqrt 2 * w))
      = c * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := fun c ↦ by
    rw [integral_const_mul, integral_comp_mul_left_Ioi (hankelIntegrand s) 0 hs2, mul_zero,
      Complex.real_smul, hankelIntegral]
    push_cast
    ring
  have hIoi : (∫ w in Set.Ioi (0 : ℝ), contourIntegrand s 0 w)
      = exp ((-(π / 4) : ℝ) * I * s) / (2 * I) *
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ contourIntegrand_zero_of_pos s hw]
    exact hscale _
  have hIic : (∫ w in Set.Iic (0 : ℝ), contourIntegrand s 0 w)
      = -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I)) *
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) := by
    have hflip := integral_comp_neg_Ioi (0 : ℝ) (contourIntegrand s 0)
    rw [neg_zero] at hflip
    rw [← hflip, setIntegral_congr_fun measurableSet_Ioi fun w hw ↦ by
      simpa only [neg_neg] using contourIntegrand_zero_of_neg s (neg_lt_zero.2 hw)]
    exact hscale _
  -- the two constant phases combine into the sine of the functional equation
  have hsum : exp ((-(π / 4) : ℝ) * I * s) / (2 * I) + -(exp ((3 * π / 4 : ℝ) * I * s) / (2 * I))
      = -(exp ((π / 4 : ℝ) * I * s) * sin ((π : ℂ) * s / 2)) := by
    rw [show ((-(π / 4) : ℝ) : ℂ) * I * s
        = ((π / 4 : ℝ) : ℂ) * I * s + -((π : ℂ) * s / 2 * I) by push_cast; ring,
      show ((3 * π / 4 : ℝ) : ℂ) * I * s
        = ((π / 4 : ℝ) : ℂ) * I * s + (π : ℂ) * s / 2 * I by push_cast; ring,
      exp_add, exp_add, ← sub_eq_add_neg, div_sub_div_same, ← mul_sub,
      div_eq_iff (by simp : (2 * I : ℂ) ≠ 0)]
    linear_combination (-exp (((π / 4 : ℝ) : ℂ) * I * s)) *
      Complex.exp_mul_I_sub_exp_neg_mul_I ((π : ℂ) * s / 2)
  -- the velocity `1 + i` of the contour, normalised, is the rotation `e^{iπ/4}`
  have hrot : (1 + I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = exp ((π / 4 : ℝ) * I) := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 :=
      mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [inv_eq_one_div, mul_one_div, div_eq_iff hne, Complex.exp_pi_div_four_mul_I]
    push_cast
    linear_combination (-(1 : ℂ) / 2 - I / 2) * h2
  rw [contourIntegral, ← intervalIntegral.integral_Iic_add_Ioi
      (integrableOn_contourIntegrand_zero_Iic hs) (integrableOn_contourIntegrand_zero_Ioi hs),
    hIic, hIoi,
    show ((π / 4 : ℝ) : ℂ) * I * (1 + s) = ((π / 4 : ℝ) : ℂ) * I + ((π / 4 : ℝ) : ℂ) * I * s by
      ring, exp_add]
  linear_combination
    ((1 + I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * hankelIntegral s) * hsum
      - (exp (((π / 4 : ℝ) : ℂ) * I * s) * sin ((π : ℂ) * s / 2) * hankelIntegral s) * hrot

end Zeta.RiemannSiegel
