/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives along an explicit chain of derivatives

A function whose successive derivatives are known one at a time, each as a closed-form expression
rather than as `deriv` of the previous one, is most cheaply differentiated by peeling off one
`iteratedDeriv` at a time.

## Main results

* `iteratedDeriv_succ_of_hasDerivAt`: if `g` is the derivative of `f` at every point, then
  `iteratedDeriv (n + 1) f = iteratedDeriv n g`.
-/
@[expose] public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f g : 𝕜 → F}

/-- **Peeling one derivative off an iterated derivative**, when the derivative is known in closed
form: if `g` is the derivative of `f` at every point, then `iteratedDeriv (n + 1) f` is the `n`-th
iterated derivative of `g`. -/
theorem iteratedDeriv_succ_of_hasDerivAt (h : ∀ x, HasDerivAt f (g x) x) (n : ℕ) :
    iteratedDeriv (n + 1) f = iteratedDeriv n g := by
  rw [iteratedDeriv_succ', funext fun x ↦ (h x).deriv]
