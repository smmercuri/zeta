/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Zeta.Analysis.Calculus.IteratedDeriv

/-!
# Iterated derivatives of the restriction to `ℝ` of an entire function

The iterated form of `HasDerivAt.real_of_complex` for an entire function.

## Main results

* `Differentiable.iteratedDeriv_re_of_complex`: for entire `e`, the `n`-th derivative of
  `fun x : ℝ ↦ (e x).re` is the real part of the `n`-th derivative of `e`.
-/
@[expose] public section


open Complex

/-- The iterated derivatives along the real axis of the real part of an entire function are the
real parts of its iterated derivatives. -/
theorem Differentiable.iteratedDeriv_re_of_complex {e : ℂ → ℂ} (he : Differentiable ℂ e) (n : ℕ)
    (x : ℝ) : iteratedDeriv n (fun y : ℝ ↦ (e y).re) x = (iteratedDeriv n e x).re := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
      have hderiv : Differentiable ℂ (_root_.deriv e) := he.deriv
      have hstep : _root_.deriv (fun y : ℝ ↦ (e y).re) = fun y : ℝ ↦ (_root_.deriv e y).re :=
        funext fun y ↦ ((he _).hasDerivAt.real_of_complex).deriv
      rw [iteratedDeriv_succ', hstep, ih hderiv, ← iteratedDeriv_succ']
