/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Bernoulli.TangentNumbers

/-!
# The Knuth-Buckholtz table of the tangent polynomials

The coefficients `knuth n k` of the tangent polynomials, their recurrence, and
`tangentNumber_eq_knuth`; `Bernoulli.FoldExperiment` proves its fold correct against them. See
`Bernoulli.TangentNumbers` for the underlying definitions and theory.
-/
@[expose] public section

namespace TangentNumbers

noncomputable section
open Polynomial

/-! ## The Knuth-Buckholtz table

The coefficients `T_{n,k}` of the tangent polynomials, `knuth n k = (tangentPoly n).coeff k`, and
their recurrence. -/

/-- The Knuth-Buckholtz numbers `T_{n,k}`: the coefficient of `tanᵏ` in the `n`-th derivative,
`dⁿ/dxⁿ tan x = Σₖ T_{n,k} · tanᵏ x`. -/
def knuth (n k : ℕ) : ℕ := (tangentPoly n).coeff k

@[simp, grind =] theorem knuth_zero (k : ℕ) : knuth 0 k = if k = 1 then 1 else 0 := by
  grind [knuth, tangentPoly, coeff_X]

/-- The first column: `T_{n+1,0} = T_{n,1}` (the `k = 0` case of Knuth's recurrence (7),
where the `T_{n,-1}` term vanishes). -/
theorem knuth_succ_zero (n : ℕ) : knuth (n + 1) 0 = knuth n 1 := by
  rw [knuth, knuth, tangentPoly_succ, add_mul, one_mul, coeff_add, coeff_derivative]
  simp

/-- Knuth's recurrence (7), in the underflow-free form
`T_{n+1,k+1} = k·T_{n,k} + (k+2)·T_{n,k+2}`
(set `k ↦ k+1` in `T_{n+1,k} = (k-1)·T_{n,k-1} + (k+1)·T_{n,k+1}`). -/
theorem knuth_succ (n k : ℕ) :
    knuth (n + 1) (k + 1) = k * knuth n k + (k + 2) * knuth n (k + 2) := by
  simp only [knuth, tangentPoly_succ, add_mul, one_mul, coeff_add]
  grind [coeff_X_pow_mul', coeff_derivative]

/-- Above the main diagonal the table vanishes: `T_{n,k} = 0` for `k > n+1`
(`Pₙ` has degree `n+1`). -/
theorem knuth_eq_zero (n k : ℕ) (hk : n + 1 < k) : knuth n k = 0 := by
  induction n generalizing k with
  | zero => grind
  | succ => grind [knuth_succ, cases Nat]

/-- The tangent number `Tₙ` is the bottom entry `T_{2n-1,0}` of the table: both are the constant
term `P_{2n-1}(0)` of the tangent polynomial. -/
theorem tangentNumber_eq_knuth (n : ℕ) : tangentNumber n = knuth (2 * n - 1) 0 := by
  rw [tangentNumber, knuth, coeff_zero_eq_eval_zero]

end

end TangentNumbers
