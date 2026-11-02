/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Zeta.RiemannSiegel.Line

/-!
# Gaussians along the slanted Riemann–Siegel contour

A Gaussian `x ↦ e^{iπ(x - c)²}` integrated along the slanted contour `Zeta.RiemannSiegel.line`
evaluates to the single constant `e^{iπ/4}`, whatever the abscissa `a` of the contour and whatever
the centre `c` (`riemann_siegel_zero.tex`, `lem:rsz_gauss_integral`).

It is that exact evaluation, not any modulus bound, that makes the Gaussian expansion of the kernel
in `Zeta/RiemannSiegel/Kernel.lean` usable: on `L(a)` the modulus of each Gaussian is enormous, and
only the cancellation recorded here recovers a bounded value.

The first-order formula (`riemann_siegel_first.tex`, `lem:rsf_gauss`) needs the same evaluation for
the rescaled Gaussian `v ↦ e^{2πi(v - c)²}`, whose value `(1 + i)/2 = e^{iπ/4}/√2` is again
independent of both the abscissa and the centre; there the centre is genuinely complex. Both are
instances of one evaluation at an arbitrary positive scale `k`.

## Main results

* `Zeta.RiemannSiegel.mul_pi_mul_I_mul_line_sub_sq`: the exponent `kiπ(x - c)²` restricted to `L(a)`
  is a quadratic in the contour parameter, with leading coefficient `-2kπ`;
* `Zeta.RiemannSiegel.integrable_exp_mul_pi_mul_I_mul_line_sub_sq`,
  `Zeta.RiemannSiegel.integral_exp_mul_pi_mul_I_mul_line_sub_sq`:
  `∫_{L(a)} e^{kiπ(x - c)²} dx = e^{iπ/4}/√k`, for `0 < k`;
* `Zeta.RiemannSiegel.integral_exp_pi_mul_I_mul_line_sub_sq`:
  `∫_{L(a)} e^{iπ(x - c)²} dx = e^{iπ/4}`;
* `Zeta.RiemannSiegel.integrable_exp_two_pi_mul_I_mul_line_sub_sq`,
  `Zeta.RiemannSiegel.integral_exp_two_pi_mul_I_mul_line_sub_sq`:
  `∫_{L(a)} e^{2πi(v - c)²} dv = (1 + i)/2`.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- **The exponent of a rescaled Gaussian along the slanted contour is a quadratic** in the contour
parameter, with leading coefficient `-2kπ`. -/
theorem mul_pi_mul_I_mul_line_sub_sq (k : ℂ) (a : ℝ) (c : ℂ) (w : ℝ) :
    k * π * I * (line a w - c) ^ 2
      = -2 * k * π * (w : ℂ) ^ 2 + 2 * k * π * I * ((a : ℂ) - c) * (1 + I) * (w : ℂ)
        + k * π * I * ((a : ℂ) - c) ^ 2 := by
  simp only [line, Complex.ofReal_add]
  -- the velocity of `L(a)` is `1 + I`, whose square is `2I`; the coefficient below is the
  -- cofactor of `I² + 1` in the difference of the two sides
  linear_combination (k * (π : ℂ) * (w : ℂ) ^ 2 * (I + 2)) * Complex.I_sq

/-- **A rescaled Gaussian is absolutely integrable along the slanted contour.** -/
theorem integrable_exp_mul_pi_mul_I_mul_line_sub_sq {k : ℝ} (hk : 0 < k) (a : ℝ) (c : ℂ) :
    Integrable fun w : ℝ ↦ exp ((k : ℂ) * π * I * (line a w - c) ^ 2) := by
  have hb : (-2 * (k : ℂ) * π).re < 0 := by simpa using mul_pos (mul_pos two_pos hk) Real.pi_pos
  exact (integrable_cexp_quadratic' hb _ _).congr
    (.of_forall fun w ↦ (congrArg exp (mul_pi_mul_I_mul_line_sub_sq k a c w)).symm)

/-- **A rescaled Gaussian integrates along the slanted contour to `e^{iπ/4}/√k`**, whatever the
abscissa `a` of the contour and whatever the centre `c`, which may be complex. -/
theorem integral_exp_mul_pi_mul_I_mul_line_sub_sq {k : ℝ} (hk : 0 < k) (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp ((k : ℂ) * π * I * (line a w - c) ^ 2)
      = exp ((π / 4 : ℝ) * I) / (Real.sqrt k : ℂ) := by
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.2 hk.ne'
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hb : (-2 * (k : ℂ) * π).re < 0 := by simpa using mul_pos (mul_pos two_pos hk) Real.pi_pos
  have hval : (k : ℂ) * π * I * ((a : ℂ) - c) ^ 2
      - (2 * k * π * I * ((a : ℂ) - c) * (1 + I)) ^ 2 / (4 * (-2 * (k : ℂ) * π)) = 0 := by
    rw [show (2 * (k : ℂ) * π * I * ((a : ℂ) - c) * (1 + I)) ^ 2
        = -8 * (k : ℂ) ^ 2 * π ^ 2 * I * ((a : ℂ) - c) ^ 2 by
      -- the cofactor of `I² + 1`
      linear_combination (4 * (k : ℂ) ^ 2 * (π : ℂ) ^ 2 * ((a : ℂ) - c) ^ 2 * (I ^ 2 + 2 * I)) *
        Complex.I_sq]
    field_simp
    ring
  have hhalf : ((π : ℂ) / -(-2 * (k : ℂ) * π)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt 2 / 2 : ℝ) : ℂ) / (Real.sqrt k : ℂ) := by
    rw [show (π : ℂ) / -(-2 * (k : ℂ) * π) = ((1 / (2 * k) : ℝ) : ℂ) by push_cast; field_simp,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, show Real.sqrt (1 / (2 * k)) = Real.sqrt 2 / 2 / Real.sqrt k by
        rw [show (1 : ℝ) / (2 * k) = (Real.sqrt 2 / 2 / Real.sqrt k) ^ 2 by
          rw [div_pow, div_pow, Real.sq_sqrt hk.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp, Real.sqrt_sq (by positivity)]]
    push_cast
    ring
  simp only [mul_pi_mul_I_mul_line_sub_sq]
  rw [integral_cexp_quadratic hb, hhalf, hval, exp_zero, mul_one, exp_pi_div_four_mul_I]
  push_cast
  ring

/-- **A Gaussian integrates along the slanted contour to `e^{iπ/4}`**, whatever the abscissa `a` of
the contour and whatever the centre `c`, which may be complex: only the reality of `a`, which fixes
the contour, is used. -/
theorem integral_exp_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp (π * I * (line a w - c) ^ 2) = exp ((π / 4 : ℝ) * I) := by
  simpa using integral_exp_mul_pi_mul_I_mul_line_sub_sq one_pos a c

/-- **The rescaled Gaussian is absolutely integrable along the slanted contour.** -/
theorem integrable_exp_two_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    Integrable fun w : ℝ ↦ exp (2 * π * I * (line a w - c) ^ 2) := by
  simpa using integrable_exp_mul_pi_mul_I_mul_line_sub_sq two_pos a c

/-- **The rescaled Gaussian integrates along the slanted contour to `(1 + i)/2`**, whatever the
abscissa `a` of the contour and whatever the centre `c`. -/
theorem integral_exp_two_pi_mul_I_mul_line_sub_sq (a : ℝ) (c : ℂ) :
    (1 + I) * ∫ w : ℝ, exp (2 * π * I * (line a w - c) ^ 2) = (1 + I) / 2 := by
  rw [← exp_pi_div_four_mul_I_div_sqrt_two]
  simpa using integral_exp_mul_pi_mul_I_mul_line_sub_sq two_pos a c

end Zeta.RiemannSiegel
