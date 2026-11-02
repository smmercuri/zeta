/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The argument on the right half-plane

Mathlib computes `Complex.arg` through `Real.arcsin` and knows `Real.tan (arg z) = z.im / z.re`,
but records no formula for `arg` in terms of `Real.arctan`. On the open right half-plane the
argument lies in `(-π/2, π/2)`, where `Real.arctan` inverts `Real.tan`, so the two are related by
the expected formula.

Rotating a point by `e^{iθ}` adds `θ` to its argument, but only up to the branch: mathlib records
this modulo `2π` as an identity of `Real.Angle` (`Complex.arg_mul_coe_angle`), whereas what an
explicit branch computation needs is the identity of real numbers, under the hypothesis that keeps
the sum inside the principal range.

## Main results

* `Complex.arg_eq_arctan`: `arg z = arctan (z.im / z.re)` whenever `0 < z.re`;
* `Complex.arg_exp_ofReal_mul_I_mul`: `arg (e^{iθ} x) = arg x + θ` whenever `arg x + θ ∈ (-π, π]`.
-/
@[expose] public section


open scoped Real

namespace Complex

/-- **On the open right half-plane the argument is the arctangent of the slope.** -/
theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  obtain ⟨h₁, h₂⟩ := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hz))
  rw [← tan_arg z, Real.arctan_tan h₁ h₂]

/-- **Rotation adds to the argument**, as an identity of real numbers, whenever the rotated argument
stays in the principal range `(-π, π]`. -/
theorem arg_exp_ofReal_mul_I_mul {θ : ℝ} {x : ℂ} (hx : x ≠ 0)
    (hθ : arg x + θ ∈ Set.Ioc (-π) π) : arg (exp ((θ : ℂ) * I) * x) = arg x + θ := by
  have hrot : exp ((θ : ℂ) * I) * x
      = (‖x‖ : ℂ) * (cos ((arg x + θ : ℝ) : ℂ) + sin ((arg x + θ : ℝ) : ℂ) * I) := by
    rw [← exp_mul_I]
    push_cast
    rw [show ((arg x : ℂ) + (θ : ℂ)) * I = (arg x : ℂ) * I + (θ : ℂ) * I by ring, exp_add,
      ← mul_assoc, norm_mul_exp_arg_mul_I, mul_comm]
  rw [hrot, arg_mul_cos_add_sin_mul_I (norm_pos_iff.2 hx) hθ]

end Complex
