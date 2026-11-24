/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Powers on the critical line and in polar form

Facts about Mathlib's principal `Complex.cpow` that it does not record: its value at a number in
polar form `r e^{iθ}`, a positive real factor splitting out, and the real part of a unit-phase
Dirichlet term `e^{iθ} x^{-(½+it)}` on the critical line.

## Main results

* `Complex.ofReal_mul_exp_mul_I_cpow`: `(r e^{iθ})^u = r^u e^{iθu}` for `r > 0` and
  `θ ∈ (-π, π]`;
* `Complex.re_exp_mul_I_mul_cpow_neg`:
  `Re (e^{iθ} x^{-(½+it)}) = cos (θ − t log x)/√x` for `x > 0`;
* `Complex.ofReal_mul_cpow`: `(r z)^u = r^u z^u` for `r > 0` real.
-/
@[expose] public section


open scoped Real

namespace Complex

/-- **The principal power of a complex number in polar form.** -/
theorem ofReal_mul_exp_mul_I_cpow {r θ : ℝ} (hr : 0 < r) (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) (u : ℂ) :
    ((r : ℂ) * exp ((θ : ℝ) * I)) ^ u = (r : ℂ) ^ u * exp ((θ : ℝ) * I * u) := by
  have hx : (r : ℂ) * exp ((θ : ℝ) * I) = exp ((Real.log r : ℂ) + (θ : ℝ) * I) := by
    rw [exp_add, ← Complex.ofReal_exp, Real.exp_log hr]
  have him : ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im = θ := by simp
  have h₁ : -π < ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im := by rw [him]; exact hθ₁
  have h₂ : ((Real.log r : ℂ) + ((θ : ℝ) : ℂ) * I).im ≤ π := by rw [him]; exact hθ₂
  rw [hx, cpow_def_of_ne_zero (exp_ne_zero _), log_exp h₁ h₂,
    cpow_def_of_ne_zero (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0),
    ← Complex.ofReal_log hr.le, ← exp_add]
  congr 1
  ring

/-- **A positive real factor splits out of a principal power.** -/
theorem ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0) (u : ℂ) :
    ((r : ℂ) * z) ^ u = (r : ℂ) ^ u * z ^ u := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hz), cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hz,
    ← exp_add, log_ofReal_mul hr hz, ofReal_log hr.le]
  ring_nf

/-- The real part of a unit-phase Dirichlet term on the critical line. -/
theorem re_exp_mul_I_mul_cpow_neg {x : ℝ} (hx : 0 < x) (t θ : ℝ) :
    (exp (I * θ) * (x : ℂ) ^ (-(1 / 2 + t * I))).re
      = Real.cos (θ - t * Real.log x) / Real.sqrt x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hsqrt : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, ← Real.exp_neg]
    congr 1
    ring
  have hz : exp (I * θ) * (x : ℂ) ^ (-(1 / 2 + t * I))
      = exp (((-Real.log x / 2 : ℝ) : ℂ) + ((θ - t * Real.log x : ℝ) : ℂ) * I) := by
    rw [cpow_def_of_ne_zero hx0, ← ofReal_log hx.le, ← exp_add]
    congr 1
    push_cast
    ring
  rw [hz, exp_re, add_re, add_im, ofReal_re, ofReal_im, re_ofReal_mul, im_ofReal_mul, I_re, I_im,
    mul_zero, mul_one, add_zero, zero_add, hsqrt]
  ring

end Complex
