/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Zeta.Analysis.Complex.Arg
public import Zeta.Analysis.Complex.Cpow
public import Zeta.RiemannSiegel.Line

/-!
# The branch of `x ^ s` along the slanted Riemann–Siegel contour

The Riemann–Siegel integrand carries a factor `x ^ (-s)` which must be interpreted through the
branch of the logarithm that is real on `(0, ∞)` and continuous on the plane cut along the *upward*
imaginary ray `i[0, ∞)` (`riemann_siegel.tex`, `def:rs_power`). Mathlib's principal branch cuts
along the negative real axis, which the slanted contour `Zeta.RiemannSiegel.line` crosses.

Rotating by `e^{iπ/4}` carries the contour into the open right half-plane
(`Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`), where the principal branch is
continuous, so the required branch is defined by rotating, taking mathlib's `cpow`, and rotating
back:
`x ^ s = e^{-iπs/4} (e^{iπ/4} x) ^ s`.

Holomorphy is stated under membership of `Complex.slitPlane`, the hypothesis of the underlying
`Complex.cpow`. The inequality `0 < Re (e^{iπ/4} x)` holds on `L(a)` for `a > 0` but becomes an
equality on the contour `L(0)` through the origin, along which the branch is holomorphic away
from `0`.

## Main results

* `Zeta.RiemannSiegel.slantArg`, `Zeta.RiemannSiegel.slantLog`,
  `Zeta.RiemannSiegel.slantCpow`: the branch of the argument, of the logarithm and of
  `x ↦ x ^ s` adapted to the contour;
* `Zeta.RiemannSiegel.slantCpow_eq_exp_mul_slantLog`: `x ^ s = e^{s Log x}`, for every `x ≠ 0`;
* `Zeta.RiemannSiegel.slantLog_eq_log`: on the right half-plane the branch agrees with mathlib's;
* `Zeta.RiemannSiegel.slantCpow_of_exp_pi_div_four_mul_I_mul_eq`: the branch in polar form,
  `x ^ u = ρ^u e^{i(φ - π/4)u}` when the rotation carries `x` to `ρ e^{iφ}`;
* `Zeta.RiemannSiegel.slantCpow_ofReal`: on `(0, ∞)` the branch agrees with mathlib's;
* `Zeta.RiemannSiegel.slantCpow_ofReal_mul_exp_pi_div_four_mul_I`,
  `Zeta.RiemannSiegel.slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I`: the branch on the two
  halves `ρ e^{iπ/4}` and `ρ e^{-3iπ/4}` of the contour through the origin;
* `Zeta.RiemannSiegel.differentiableAt_slantCpow`: the branch is holomorphic off the rotated branch
  cut;
* `Zeta.RiemannSiegel.norm_slantCpow`: `‖x ^ s‖ = ‖x‖ ^ Re s / exp (slantArg x * Im s)`;
* `Zeta.RiemannSiegel.slantArg_line`, `Zeta.RiemannSiegel.abs_slantArg_line_lt`: along the contour
  the argument is `arctan ((a + 2w)/a) - π/4`, and in particular bounded by `3π/4`;
* `Zeta.RiemannSiegel.slantArg_line_mul_im_le`: the resulting bound on the exponent of the modulus
  of the power.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- The argument rotated through `π/4`, `slantArg x = arg (e^{iπ/4} x) - π/4`. On the rotated
right half-plane `Re (e^{iπ/4} x) > 0` (which contains the whole contour
`Zeta.RiemannSiegel.line a` for `a > 0`) it is the branch of the argument that is continuous on
the plane cut along the upward imaginary ray `i[0, ∞)`. -/
noncomputable def slantArg (x : ℂ) : ℝ := (exp ((π / 4 : ℝ) * I) * x).arg - π / 4

/-- The branch of the logarithm cut along the upward imaginary ray,
`Log x = log ‖x‖ + i arg_Ω x` with `arg_Ω = Zeta.RiemannSiegel.slantArg`. It is the branch that is
real on `(0, ∞)` and continuous on `ℂ \ i[0, ∞)`. -/
noncomputable def slantLog (x : ℂ) : ℂ := (Real.log ‖x‖ : ℂ) + (slantArg x : ℂ) * I

/-- The branch of `x ↦ x ^ s` cut along the upward imaginary ray, `x ^ s = e^{-iπs/4}
(e^{iπ/4} x) ^ s` with Mathlib's principal `Complex.cpow` on the right. It agrees with the principal
branch on `(0, ∞)`, and on the rotated right half-plane it is the branch determined by
`Zeta.RiemannSiegel.slantArg`. -/
noncomputable def slantCpow (x s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I * s)) * (exp ((π / 4 : ℝ) * I) * x) ^ s

/-- The slanted power is the exponential of the slanted logarithm, `x ^ s = e^{s Log x}`, for
every `x ≠ 0`: the branch cut of the rotated variable is invisible to both sides. -/
theorem slantCpow_eq_exp_mul_slantLog {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    slantCpow x s = exp (s * slantLog x) := by
  rw [slantCpow, Complex.cpow_def_of_ne_zero (mul_ne_zero (exp_ne_zero _) hx), ← exp_add,
    Complex.log, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, slantLog, slantArg]
  congr 1
  push_cast
  ring

/-- On the right half-plane the slanted logarithm is mathlib's principal one. -/
theorem slantLog_eq_log {x : ℂ} (hx : 0 < x.re) : slantLog x = Complex.log x := by
  have hpi := Real.pi_pos
  obtain ⟨h₁, h₂⟩ := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hx))
  rw [slantLog, slantArg, Complex.arg_exp_ofReal_mul_I_mul (fun h ↦ by simp [h] at hx)
    ⟨by linarith, by linarith⟩, add_sub_cancel_right, Complex.log]

/-- The slanted power in polar form: if the rotation carries `x` to `ρ e^{iφ}` with `ρ > 0` and
`φ ∈ (-π, π]`, then `x ^ u = ρ^u e^{i(φ - π/4)u}`. -/
theorem slantCpow_of_exp_pi_div_four_mul_I_mul_eq {x : ℂ} {ρ φ : ℝ} (hρ : 0 < ρ) (hφ₁ : -π < φ)
    (hφ₂ : φ ≤ π) (hx : exp ((π / 4 : ℝ) * I) * x = (ρ : ℂ) * exp ((φ : ℝ) * I)) (u : ℂ) :
    slantCpow x u = (ρ : ℂ) ^ u * exp ((φ - π / 4 : ℝ) * I * u) := by
  rw [slantCpow, hx, Complex.ofReal_mul_exp_mul_I_cpow hρ hφ₁ hφ₂ u, ← mul_assoc,
    mul_comm (exp (-(((π / 4 : ℝ) : ℂ) * I * u))) ((ρ : ℂ) ^ u), mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- On the positive reals the slanted branch agrees with Mathlib's principal one. -/
theorem slantCpow_ofReal {r : ℝ} (hr : 0 < r) (s : ℂ) : slantCpow (r : ℂ) s = (r : ℂ) ^ s := by
  have hpi := Real.pi_pos
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hr (φ := π / 4) (by linarith) (by linarith)
    (mul_comm _ _) s, sub_self, Complex.ofReal_zero, zero_mul, zero_mul, exp_zero, mul_one]

/-- The slanted branch on the outgoing Hankel ray `ρ e^{iπ/4}`, where `arg_Ω` is `π/4`. -/
theorem slantCpow_ofReal_mul_exp_pi_div_four_mul_I {ρ : ℝ} (hρ : 0 < ρ) (u : ℂ) :
    slantCpow ((ρ : ℂ) * exp ((π / 4 : ℝ) * I)) u = (ρ : ℂ) ^ u * exp ((π / 4 : ℝ) * I * u) := by
  have hpi := Real.pi_pos
  have hrot : exp ((π / 4 : ℝ) * I) * ((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = (ρ : ℂ) * exp ((π / 2 : ℝ) * I) := by
    rw [show ((π / 2 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by push_cast; ring, exp_pi_div_two_mul_I]
    linear_combination (ρ : ℂ) * Complex.exp_pi_div_four_mul_I_mul_self
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hρ (by linarith) (by linarith) hrot u,
    show π / 2 - π / 4 = π / 4 by ring]

/-- The slanted branch on the incoming Hankel ray `ρ e^{-3iπ/4}`, where `arg_Ω` is `-3π/4`. -/
theorem slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I {ρ : ℝ} (hρ : 0 < ρ) (u : ℂ) :
    slantCpow (-((ρ : ℂ) * exp ((π / 4 : ℝ) * I))) u
      = (ρ : ℂ) ^ u * exp ((-(3 * π / 4) : ℝ) * I * u) := by
  have hpi := Real.pi_pos
  have hrot : exp ((π / 4 : ℝ) * I) * -((ρ : ℂ) * exp ((π / 4 : ℝ) * I))
      = (ρ : ℂ) * exp ((-(π / 2) : ℝ) * I) := by
    rw [show ((-(π / 2) : ℝ) : ℂ) * I = -((π : ℂ) / 2 * I) by push_cast; ring, exp_neg,
      exp_pi_div_two_mul_I, inv_I]
    linear_combination (-(ρ : ℂ)) * Complex.exp_pi_div_four_mul_I_mul_self
  rw [slantCpow_of_exp_pi_div_four_mul_I_mul_eq hρ (by linarith) (by linarith) hrot u,
    show -(π / 2) - π / 4 = -(3 * π / 4) by ring]

/-- The slanted branch is holomorphic off the rotated branch cut. -/
theorem differentiableAt_slantCpow (s : ℂ) {x : ℂ} (hx : exp ((π / 4 : ℝ) * I) * x ∈ slitPlane) :
    DifferentiableAt ℂ (fun y ↦ slantCpow y s) x :=
  (((by fun_prop : DifferentiableAt ℂ (fun y : ℂ ↦ exp ((π / 4 : ℝ) * I) * y) x).cpow
    (by fun_prop) hx).const_mul _)

/-- The modulus of the slanted power: `‖x ^ s‖ = ‖x‖ ^ Re s / exp (slantArg x * Im s)`. -/
theorem norm_slantCpow {x : ℂ} (hx : x ≠ 0) (s : ℂ) :
    ‖slantCpow x s‖ = ‖x‖ ^ s.re / Real.exp (slantArg x * s.im) := by
  have hre : (-(((π / 4 : ℝ) : ℂ) * I * s)).re = π / 4 * s.im := by
    simp [Complex.mul_re, Complex.mul_im]
  -- rotation is an isometry, so the rotated variable has the same modulus
  rw [slantCpow, norm_mul, Complex.norm_cpow_of_ne_zero (mul_ne_zero (exp_ne_zero _) hx),
    norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp, hre, slantArg, sub_mul,
    Real.exp_sub]
  field_simp

/-- The argument along the slanted contour. -/
theorem slantArg_line {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) = Real.arctan ((a + 2 * w) / a) - π / 4 := by
  have hre : (exp ((π / 4 : ℝ) * I) * line a w).re = Real.sqrt 2 / 2 * a := by
    rw [exp_pi_div_four_mul_I_mul_line]; simp
  have him : (exp ((π / 4 : ℝ) * I) * line a w).im = Real.sqrt 2 / 2 * (a + 2 * w) := by
    rw [exp_pi_div_four_mul_I_mul_line]; simp
  rw [slantArg, Complex.arg_eq_arctan (by rw [hre]; positivity), hre, him,
    mul_div_mul_left _ _ (by positivity : Real.sqrt 2 / 2 ≠ 0)]

/-- The slanted contour stays clear of the branch cut: its argument lies in `(-3π/4, 3π/4)`. -/
theorem abs_slantArg_line_lt {a : ℝ} (ha : 0 < a) (w : ℝ) : |slantArg (line a w)| < 3 * π / 4 := by
  rw [slantArg_line ha, abs_lt]
  exact ⟨by linarith [Real.neg_pi_div_two_lt_arctan ((a + 2 * w) / a)],
    by linarith [Real.arctan_lt_pi_div_two ((a + 2 * w) / a), Real.pi_pos]⟩

/-- The exponential factor contributed by the argument of the power is bounded along the
contour. -/
theorem slantArg_line_mul_im_le (s : ℂ) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    slantArg (line a w) * s.im ≤ 3 * π * |s.im| / 4 := by
  refine (le_abs_self _).trans ?_
  rw [abs_mul]
  nlinarith [(abs_slantArg_line_lt ha w).le, abs_nonneg s.im, abs_nonneg (slantArg (line a w))]

/-- The slanted logarithm is continuous along the contour. -/
theorem continuous_slantLog_line {a : ℝ} (ha0 : 0 < a) :
    Continuous fun w : ℝ ↦ slantLog (line a w) := by
  have hlog : Continuous fun w : ℝ ↦ Real.log ‖line a w‖ :=
    continuous_iff_continuousAt.2 fun w ↦
      (continuous_line a).norm.continuousAt.log (norm_ne_zero_iff.2 (line_ne_zero ha0.ne' w))
  simp only [slantLog, slantArg_line ha0]
  fun_prop

/-- The slanted logarithm grows at most linearly along the contour. -/
theorem norm_slantLog_line_le {a : ℝ} (ha0 : 0 < a) (w : ℝ) :
    ‖slantLog (line a w)‖ ≤ |Real.log (a / Real.sqrt 2)| + a + 3 * π / 4 + 2 * |w| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [abs_log_norm_line_le ha0 w, (abs_slantArg_line_lt ha0 w).le]

end Zeta.RiemannSiegel
