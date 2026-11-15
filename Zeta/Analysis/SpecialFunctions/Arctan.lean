/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary two-sided bounds for the arctangent

A lower bound for `Real.arctan x` on `[0, ∞)`, complementing Mathlib's `Real.arctan_le_self`.

## Main results

* `Real.div_one_add_sq_le_arctan`: `x/(1+x²) ≤ arctan x` for `x ≥ 0`.
-/
@[expose] public section


open scoped Real

namespace Real

/-- `x/(1+x²) ≤ arctan x` on `[0, ∞)`, the lower companion of `Real.arctan_le_self`. -/
theorem div_one_add_sq_le_arctan {x : ℝ} (hx : 0 ≤ x) : x / (1 + x ^ 2) ≤ arctan x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : √(1 + x ^ 2) * √(1 + x ^ 2) = 1 + x ^ 2 := mul_self_sqrt hpos.le
  have hsin : sin (2 * arctan x) = 2 * (x / (1 + x ^ 2)) := by
    rw [sin_two_mul, sin_arctan, cos_arctan, mul_assoc, div_mul_div_comm, mul_one, hsq]
  have hle : sin (2 * arctan x) ≤ 2 * arctan x := sin_le (by positivity)
  rw [hsin] at hle
  linarith

end Real
