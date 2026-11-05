/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.HalfPlane

/-!
# The trigamma recurrence for the digamma function

Basic facts about the "trigamma" function `ψ' = deriv Complex.digamma`, used in the convexity of
the Riemann–Siegel theta function (`Zeta.Gram.Averaging`, `gram_averaging.tex`).

## Main results

* `Complex.deriv_digamma_add_one`: the trigamma recurrence `ψ'(s+1) = ψ'(s) − s⁻²`;
* `Complex.im_inv_sq_nonpos`: `Im (w²)⁻¹ ≤ 0` for `w` in the closed first quadrant.
-/
@[expose] public section


namespace Complex

/-- **Trigamma recurrence.** For `Re s > 0`, `ψ'(s + 1) = ψ'(s) − s⁻²`. -/
theorem deriv_digamma_add_one {s : ℂ} (hs : 0 < s.re) :
    deriv Complex.digamma (s + 1) = deriv Complex.digamma s - (s ^ 2)⁻¹ := by
  have hs1 : 0 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  -- `ψ (· + 1)` has derivative `ψ' (s + 1)` at `s` by the chain rule ...
  have hL : HasDerivAt (fun z ↦ Complex.digamma (z + 1)) (deriv Complex.digamma (s + 1)) s := by
    simpa [Function.comp_def] using
      (differentiableAt_digamma hs1).hasDerivAt.comp s ((hasDerivAt_id s).add_const 1)
  -- ... and it agrees with `ψ + (·)⁻¹` near `s`, whose derivative is `ψ' s - s⁻²`.
  have heq : (fun z ↦ Complex.digamma (z + 1)) =ᶠ[nhds s] fun z ↦ Complex.digamma z + z⁻¹ := by
    filter_upwards [(isOpen_re_gt 0).mem_nhds hs] with z (hz : 0 < z.re)
    exact Complex.digamma_apply_add_one z (ne_neg_natCast_of_re_pos hz)
  rw [hL.unique <| ((differentiableAt_digamma hs).hasDerivAt.add
    (hasDerivAt_inv (Complex.ne_zero_of_re_pos hs))).congr_of_eventuallyEq heq]
  ring

/-- **Sign of the quadratic term.** For `w` in the closed first quadrant (`0 ≤ Re w`, `0 ≤ Im w`),
`Im (w²)⁻¹ ≤ 0`. -/
theorem im_inv_sq_nonpos {w : ℂ} (hre : 0 ≤ w.re) (him : 0 ≤ w.im) : ((w ^ 2)⁻¹).im ≤ 0 := by
  rw [Complex.inv_im, neg_div, neg_nonpos, sq, Complex.mul_im]
  exact div_nonneg (by nlinarith [mul_nonneg hre him]) (Complex.normSq_nonneg _)

end Complex
