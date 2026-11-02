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

Mathlib knows that `Real.arctan` is strictly monotone and takes values in `(-π/2, π/2)`, but
records no comparison between `arctan x` and `x` itself. Both directions are needed to expand a
principal argument `Complex.arg` to first order in a small slope.

## Main results

* `Real.arctan_le_self`: `arctan x ≤ x` for `x ≥ 0`;
* `Real.div_one_add_sq_le_arctan`: `x/(1+x²) ≤ arctan x` for `x ≥ 0`.
-/
@[expose] public section


open scoped Real

namespace Real

/-- **The arctangent is at most its argument** on `[0, ∞)`. -/
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have hlt := lt_tan (arctan_pos.2 h) (arctan_lt_pi_div_two x)
    rw [tan_arctan] at hlt
    exact hlt.le

/-- **A lower bound for the arctangent** on `[0, ∞)`, matching `Real.arctan_le_self`. -/
theorem div_one_add_sq_le_arctan {x : ℝ} (hx : 0 ≤ x) : x / (1 + x ^ 2) ≤ arctan x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : √(1 + x ^ 2) * √(1 + x ^ 2) = 1 + x ^ 2 := mul_self_sqrt hpos.le
  have hsin : sin (2 * arctan x) = 2 * (x / (1 + x ^ 2)) := by
    rw [sin_two_mul, sin_arctan, cos_arctan, mul_assoc, div_mul_div_comm, mul_one, hsq]
  have hle : sin (2 * arctan x) ≤ 2 * arctan x := sin_le (by positivity)
  rw [hsin] at hle
  linarith

end Real
