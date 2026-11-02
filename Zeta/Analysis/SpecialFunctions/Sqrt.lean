/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A telescoping bound for sums of inverse square roots

At `s = 1/2` the sum `∑ n^{-s}` diverges, so the useful statement is the sharp-order one
`∑_{n ≤ ν} n^{-1/2} ≤ 2√ν`, which mathlib does not record.

It is consumed by `Zeta/RiemannSiegel/ZeroOrder.lean`, where it converts a perturbation of the
Riemann–Siegel phase into a perturbation of the main sum.

## Main results

* `Real.sum_one_div_sqrt_le`: `∑_{n = 1}^{ν} n^{-1/2} ≤ 2√ν`.
-/
@[expose] public section


namespace Real

/-- **The inverse square roots up to `ν` sum to at most `2√ν`.** -/
theorem sum_one_div_sqrt_le (ν : ℕ) :
    ∑ n ∈ Finset.Icc 1 ν, 1 / Real.sqrt n ≤ 2 * Real.sqrt ν := by
  induction ν with
  | zero => simp
  | succ k ih =>
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hb0 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0
    have hb : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
    -- `1/√(k+1) ≤ 2(√(k+1) − √k)`, since `2(b − a) = 2/(b + a)` and `a ≤ b`
    have key : 1 / Real.sqrt ((k : ℝ) + 1)
        ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ hb0]
      nlinarith [sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ))]
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    linarith

end Real
