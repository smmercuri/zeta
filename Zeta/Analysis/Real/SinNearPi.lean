/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cubic contraction of `x ↦ x + sin x` near `π`

The map `x ↦ x + sin x` fixes `π` and contracts cubically there, which is the cubic convergence
of the classical fixed-point iteration `xₙ₊₁ = xₙ + sin xₙ → π`.

## Main results

- `Real.abs_add_sin_sub_pi_lt`: `|x - π| < δ` implies `|(x + sin x) - π| < δ³/6`.
-/
@[expose] public section


open Real

namespace Real

/-- Cubic contraction of `x ↦ x + sin x` toward `π`: `|x - π| < δ` implies
`|(x + sin x) - π| < δ³ / 6`. -/
theorem abs_add_sin_sub_pi_lt {x δ : ℝ} (h : |x - π| < δ) :
    |(x + sin x) - π| < δ ^ 3 / 6 := by
  calc _ = |(x - π) - sin (x - π)| := by grind [Real.sin_add_pi (x - π)]
    _ ≤ |x - π| ^ 3 / 6 := abs_sub_sin_le _
    _ < δ ^ 3 / 6 := by gcongr

end Real
