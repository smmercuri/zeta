/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Real.Pi.Irrational
public import Zeta.Analysis.Complex.RealDeriv
public import Zeta.RiemannSiegel.Defs
public import Zeta.RiemannSiegel.ModelShift
public import Zeta.RiemannSiegel.Moment

/-!
# The Riemann–Siegel correction function

The half shift `Zeta.RiemannSiegel.modelIntegral_add_half` and the unit shift
`Zeta.RiemannSiegel.modelIntegral_add_modelIntegral_add_one` are incompatible in a useful way:
iterating the half shift twice computes `M(p + 1)` from `M(p)` with coefficient `e^{4πip}`, whereas
the unit shift computes it with coefficient `−1`. At each fixed `p` these are two linear equations
in the two unknowns `M(p)` and `M(p + 1)`, so eliminating `M(p + 1)` determines `M(p)`
**algebraically** — with no analytic continuation, no Liouville argument and no growth estimate
(`riemann_siegel_first.tex`, `thm:rsf_model_closed` and `rem:rsf_why_algebraic`).

The resulting closed form is stated in product form, never as a quotient: the coefficient
`1 + e^{4πip}` vanishes exactly where `cos (2πp)` does, and there the right-hand side vanishes with
it. For the same reason the **correction function** `Ψ` of `def:rsf_correction`, which carries the
whole of the first-order correction to Hardy's function, is defined through `M` rather than through
the classical quotient `cos (2π(p² − p − 1/16)) / cos (2πp)`.

## Main results

* `Zeta.RiemannSiegel.two_mul_cos_mul_modelIntegral`:
  `2 cos(2πp) M(p) = e^{2πi(p² − p)} + √2 e^{5iπ/8} sin(πp)`;
* `Zeta.RiemannSiegel.correction`: the correction function `Ψ(p) = 2 Re(e^{−iπ/8} M(p))`;
* `Zeta.RiemannSiegel.cos_mul_correction`: `cos(2πp) Ψ(p) = cos(2π(p² − p − 1/16))`;
* `Zeta.RiemannSiegel.abs_correction_le`: `|Ψ(p)| ≤ e^{π/4}` on `[0, 1]`;
* `Zeta.RiemannSiegel.iteratedDeriv_three_correction`: `Ψ''' = 2 Re(e^{−iπ/8} M''')`;
* `Zeta.RiemannSiegel.neg_iteratedDeriv_three_correction_div_eq`: the linear Riemann–Siegel
  coefficient `C₁(p) = −Ψ'''(p)/(96π²)` as a combination of the moments `N₁` and `N₃`.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- **The closed form of the model integral** (`riemann_siegel_first.tex`,
`thm:rsf_model_closed`): `2 cos(2πp) M(p) = e^{2πi(p² − p)} + √2 e^{5iπ/8} sin(πp)`. It is stated in
product form because the factor `1 + e^{4πip}` eliminated in its proof vanishes exactly where
`cos (2πp)` does. -/
theorem two_mul_cos_mul_modelIntegral (p : ℂ) :
    2 * cos (2 * π * p) * modelIntegral p (1 / 2)
      = exp (2 * π * I * (p ^ 2 - p))
        + (Real.sqrt 2 : ℂ) * exp ((5 * π / 8 : ℝ) * I) * sin (π * p) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsinv : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ) / 2 := by
    rw [inv_eq_one_div, div_eq_div_iff (ofReal_ne_zero.2 (by positivity)) two_ne_zero]
    linear_combination -hs
  -- the two functional equations, the half shift being applied at `p` and at `p + 1/2`
  have h1 := modelIntegral_add_half p
  have h2 := modelIntegral_add_half (p + 1 / 2)
  have h3 := modelIntegral_add_modelIntegral_add_one p
  rw [show p + 1 / 2 + 1 / 2 = p + 1 by ring] at h2
  have h2p : exp (2 * (π : ℂ) * I * p) = exp ((π : ℂ) * I * p) ^ 2 := by
    rw [sq, ← exp_add]; congr 1; ring
  have e1 : exp (2 * (π : ℂ) * I * (p + 1 / 2)) = -exp ((π : ℂ) * I * p) ^ 2 := by
    rw [show 2 * (π : ℂ) * I * (p + 1 / 2) = 2 * π * I * p + π * I by ring, exp_add, exp_pi_mul_I,
      h2p]; ring
  have e2 : exp ((π : ℂ) * I * (p + 1 / 2)) = I * exp ((π : ℂ) * I * p) := by
    rw [show (π : ℂ) * I * (p + 1 / 2) = π * I * p + (π : ℂ) / 2 * I by ring, exp_add,
      exp_pi_div_two_mul_I]; ring
  rw [e1, e2] at h2
  rw [h2p] at h1
  set E : ℂ := exp ((π : ℂ) * I * p) with hEdef
  have hE0 : E ≠ 0 := exp_ne_zero _
  -- Eliminating `M(p + 1/2)` and `M(p + 1)` leaves a single linear equation in `M(p)`. The two
  -- trailing terms of this and of the final combination are there because `ring` treats `I` and
  -- `(√2)⁻¹` as atoms: `I² = -1` and `1/√2 = √2/2` have to be supplied explicitly.
  have hkey : (1 + E ^ 4) * modelIntegral p (1 / 2)
      = exp (2 * (π : ℂ) * I * p ^ 2)
        + E ^ 3 * exp ((π / 8 : ℝ) * I) * (((Real.sqrt 2 : ℝ) : ℂ) / 2)
        - exp ((π / 8 : ℝ) * I) * E * (((Real.sqrt 2 : ℝ) : ℂ) / 2) := by
    linear_combination h3 - h2 + (I * E ^ 2) * h1
      + (E ^ 3 * exp ((π / 8 : ℝ) * I) - exp ((π / 8 : ℝ) * I) * E) * hsinv
      + (E ^ 4 * modelIntegral p (1 / 2) + (exp ((π / 8 : ℝ) * I) * E
        - E ^ 3 * exp ((π / 8 : ℝ) * I)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * Complex.I_sq
  -- the trigonometric factors, cleared of inverses by the factor `E²`
  have hDE : exp (-(2 * (π : ℂ) * I * p)) * E ^ 2 = 1 := by
    rw [← h2p, ← exp_add, neg_add_cancel, exp_zero]
  have hFE : exp (-((π : ℂ) * I * p)) * E = 1 := by
    rw [hEdef, ← exp_add, neg_add_cancel, exp_zero]
  have hcosE : 2 * cos (2 * (π : ℂ) * p) * E ^ 2 = E ^ 4 + 1 := by
    rw [Complex.two_cos, show 2 * (π : ℂ) * p * I = 2 * π * I * p by ring,
      show -(2 * (π : ℂ) * p) * I = -(2 * π * I * p) by ring, h2p]
    linear_combination hDE
  have hsinE : 2 * sin ((π : ℂ) * p) * E ^ 2 = (E - E ^ 3) * I := by
    have h := Complex.two_sin ((π : ℂ) * p)
    rw [show (π : ℂ) * p * I = π * I * p by ring,
      show -((π : ℂ) * p) * I = -((π : ℂ) * I * p) by ring, ← hEdef] at h
    rw [show 2 * sin ((π : ℂ) * p) * E ^ 2 = (2 * sin ((π : ℂ) * p)) * E ^ 2 by ring, h]
    linear_combination (E * I) * hFE
  have hQE : exp (2 * (π : ℂ) * I * (p ^ 2 - p)) * E ^ 2 = exp (2 * (π : ℂ) * I * p ^ 2) := by
    rw [← h2p, ← exp_add]; congr 1; ring
  have h5 : exp ((5 * π / 8 : ℝ) * I) = I * exp ((π / 8 : ℝ) * I) := by
    rw [show ((5 * π / 8 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I + ((π / 8 : ℝ) : ℂ) * I by
      push_cast; ring, exp_add, exp_pi_div_two_mul_I]
  refine mul_right_cancel₀ (pow_ne_zero 2 hE0) ?_
  linear_combination (modelIntegral p (1 / 2)) * hcosE + hkey - hQE
    - (((Real.sqrt 2 : ℝ) : ℂ) * I * exp ((π / 8 : ℝ) * I) / 2) * hsinE
    - (((Real.sqrt 2 : ℝ) : ℂ) * sin ((π : ℂ) * p) * E ^ 2) * h5
    - (((Real.sqrt 2 : ℝ) : ℂ) * exp ((π / 8 : ℝ) * I) * (E - E ^ 3) / 2) * Complex.I_sq

/-- **The closed form of the correction function** (`riemann_siegel_first.tex`,
`cor:rsf_correction_closed`): `cos(2πp) Ψ(p) = cos(2π(p² − p − 1/16))`, so that
`Ψ(p) = cos(2π(p² − p − 1/16))/cos(2πp)` wherever the quotient is defined. -/
theorem cos_mul_correction (p : ℝ) :
    Real.cos (2 * π * p) * correction p = Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) := by
  have hG : exp (-((π / 8 : ℝ) * I)) * ((Real.sqrt 2 : ℂ) * exp ((5 * π / 8 : ℝ) * I))
      = (Real.sqrt 2 : ℂ) * I := by
    rw [show exp (-(((π / 8 : ℝ) : ℂ) * I)) * ((Real.sqrt 2 : ℂ) * exp (((5 * π / 8 : ℝ) : ℂ) * I))
        = (Real.sqrt 2 : ℂ) *
          (exp (-(((π / 8 : ℝ) : ℂ) * I)) * exp (((5 * π / 8 : ℝ) : ℂ) * I)) by ring,
      ← exp_add, show -(((π / 8 : ℝ) : ℂ) * I) + ((5 * π / 8 : ℝ) : ℂ) * I = (π : ℂ) / 2 * I by
        push_cast; ring, exp_pi_div_two_mul_I]
  have hQ : exp (-((π / 8 : ℝ) * I)) * exp (2 * (π : ℂ) * I * ((p : ℂ) ^ 2 - (p : ℂ)))
      = exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I) := by
    rw [← exp_add]; congr 1; push_cast; ring
  -- multiply the closed form by `e^{-iπ/8}`, in which the sine term becomes purely imaginary
  have key : 2 * ((Real.cos (2 * π * p) : ℝ) : ℂ) *
      (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2))
      = exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I)
        + (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ) := by
    have h := two_mul_cos_mul_modelIntegral (p : ℂ)
    rw [show (2 : ℂ) * π * (p : ℂ) = ((2 * π * p : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
      show ((π : ℂ)) * (p : ℂ) = ((π * p : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin] at h
    linear_combination exp (-((π / 8 : ℝ) * I)) * h + hQ +
      ((Real.sin (π * p) : ℝ) : ℂ) * hG
  -- the real part of the left side is `cos(2πp) Ψ(p)`, that of the sine term is zero
  have hL : (2 * ((Real.cos (2 * π * p) : ℝ) : ℂ) *
      (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2))).re
      = Real.cos (2 * π * p) * correction p := by
    rw [show (2 : ℂ) * ((Real.cos (2 * π * p) : ℝ) : ℂ)
        = ((2 * Real.cos (2 * π * p) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      correction]
    ring
  have hR : (exp (((2 * π * (p ^ 2 - p - 1 / 16) : ℝ) : ℂ) * I)
      + (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ)).re
      = Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) := by
    rw [Complex.add_re, Complex.exp_ofReal_mul_I_re,
      show (Real.sqrt 2 : ℂ) * I * ((Real.sin (π * p) : ℝ) : ℂ)
        = ((Real.sqrt 2 * Real.sin (π * p) : ℝ) : ℂ) * I by push_cast; ring]
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
  rw [← hL, ← hR, key]

/-- **The classical quotient form of `Ψ` is defined at every rational height.** For rational
`q > 0` the Riemann–Siegel fractional part `p = √(q/2π) − ⌊√(q/2π)⌋₊` never lands on `1/4` or
`3/4`, so `cos(2πp) ≠ 0` and `cos_mul_correction` may be divided through. Indeed `cos(2πp) = 0`
forces `p = (2k+1)/4`, hence `√(q/2π) = M/4` is rational and `π = 8q/M²`, contradicting
`irrational_pi`. -/
theorem cos_two_pi_fract_sqrt_ne_zero (q : ℚ) (hq : 0 < q) :
    Real.cos (2 * Real.pi *
        (Real.sqrt ((q : ℝ) / (2 * Real.pi)) - ⌊Real.sqrt ((q : ℝ) / (2 * Real.pi))⌋₊)) ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set s : ℝ := Real.sqrt ((q : ℝ) / (2 * Real.pi)) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = (q : ℝ) / (2 * Real.pi) := Real.sq_sqrt (by positivity)
  intro hcos
  obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hcos
  have hfrac : 4 * (s - (⌊s⌋₊ : ℝ)) = 2 * (k : ℝ) + 1 := by
    refine mul_left_cancel₀ hpi0 ?_
    ring_nf
    ring_nf at hk
    linarith
  set M : ℤ := 4 * (⌊s⌋₊ : ℤ) + 2 * k + 1 with hMdef
  have hsM : s = (M : ℝ) / 4 := by
    have : (M : ℝ) = 4 * (⌊s⌋₊ : ℝ) + 2 * (k : ℝ) + 1 := by push_cast [hMdef]; ring
    rw [this]; linarith
  have hM0 : (M : ℝ) ≠ 0 := by
    intro h; rw [h] at hsM; simp at hsM; linarith
  have hpiRat : ((8 * q / (M : ℚ) ^ 2 : ℚ) : ℝ) = Real.pi := by
    have hMQ : ((M : ℚ) : ℝ) ^ 2 ≠ 0 := by push_cast; exact pow_ne_zero 2 hM0
    have h1 : (M : ℝ) ^ 2 / 16 = (q : ℝ) / (2 * Real.pi) := by rw [← hsq, hsM]; ring
    have h2 : 2 * Real.pi * ((M : ℝ) ^ 2 / 16) = (q : ℝ) := by rw [h1]; field_simp
    push_cast
    field_simp
    linarith [h2]
  exact irrational_pi ⟨8 * q / (M : ℚ) ^ 2, hpiRat⟩

/-- **The correction function is bounded by `e^{π/4}`** on the unit interval. -/
theorem abs_correction_le {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    |correction p| ≤ Real.exp (π / 4) := by
  have hunit : ‖exp (-((π / 8 : ℝ) * I))‖ = 1 := by simp [Complex.norm_exp]
  have hre : |(exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re|
      ≤ Real.exp (π * (1 / 2 - p) ^ 2) / 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, hunit, one_mul]
    exact norm_modelIntegral_le p
  calc |correction p|
      = 2 * |(exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re| := by
        rw [correction, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ Real.exp (π * (1 / 2 - p) ^ 2) := by linarith
    _ ≤ Real.exp (π / 4) :=
        Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, mul_nonneg h0 (sub_nonneg.2 h1)])

/-- **The third derivative of the correction function in terms of the model integral**
(`riemann_siegel_first.tex`, `lem:rsf_moment_deriv`): `Ψ''' = 2 Re(e^{−iπ/8} M''')`. -/
theorem iteratedDeriv_three_correction (p : ℝ) :
    iteratedDeriv 3 correction p
      = 2 * (exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)).re := by
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z ↦ by simp
  have hM : Differentiable ℂ fun q : ℂ ↦ modelIntegral q (1 / 2) := by
    simpa only [modelMoment_zero] using
      differentiable_modelMoment 0 (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)
  have hcorr : correction = fun x : ℝ ↦
      (2 * exp (-((π / 8 : ℝ) * I)) * modelIntegral (x : ℂ) (1 / 2)).re := by
    funext x
    rw [correction, mul_assoc, h2]
  rw [hcorr, (hM.const_mul (2 * exp (-((π / 8 : ℝ) * I)))).iteratedDeriv_re_of_complex 3 p,
    iteratedDeriv_const_mul_field, mul_assoc, h2]

/-- **The linear Riemann–Siegel coefficient as a moment combination**
(`riemann_siegel_first.tex`, `lem:rsf_c1`):
`C₁(p) = −Ψ'''(p)/(96π²) = 2 Re(e^{−iπ/8}(−N₁/2 − (2πi/3) N₃))`. -/
theorem neg_iteratedDeriv_three_correction_div_eq (p : ℝ) :
    -iteratedDeriv 3 correction p / (96 * π ^ 2)
      = 2 * (exp (-((π / 8 : ℝ) * I)) *
          (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2)
            - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re := by
  have hc : (96 : ℂ) * (π : ℂ) ^ 2 = ((96 * π ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [neg_half_modelMoment_one_sub_eq (p : ℂ) (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2),
    iteratedDeriv_three_correction p, hc,
    show exp (-((π / 8 : ℝ) * I)) *
        (-iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) /
          ((96 * π ^ 2 : ℝ) : ℂ))
      = -(exp (-((π / 8 : ℝ) * I)) *
          iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)) /
            ((96 * π ^ 2 : ℝ) : ℂ) by ring, Complex.div_ofReal_re, Complex.neg_re]
  ring

private noncomputable def modelCorrection (q : ℂ) : ℂ :=
  2 * exp (-((π / 8 : ℝ) * I)) * modelIntegral q (1 / 2)

private theorem differentiable_modelCorrection : Differentiable ℂ modelCorrection := by
  have hM : Differentiable ℂ fun q : ℂ ↦ modelIntegral q (1 / 2) := by
    simpa only [modelMoment_zero] using
      differentiable_modelMoment 0 (by norm_num : (1 : ℝ) / 2 = (0 : ℤ) + 1 / 2)
  exact hM.const_mul _

private theorem correction_eq_re : correction = fun x : ℝ ↦ (modelCorrection (x : ℂ)).re := by
  funext x
  have h2 : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z ↦ by simp
  rw [correction, modelCorrection, mul_assoc, h2]

private theorem differentiable_iteratedDeriv_modelCorrection (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k modelCorrection) := by
  induction k with
  | zero => simpa using differentiable_modelCorrection
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- **Every iterated derivative of `Ψ` is differentiable** — it is the real part along `ℝ` of the
corresponding derivative of an entire function. -/
theorem differentiable_iteratedDeriv_correction (k : ℕ) :
    Differentiable ℝ (iteratedDeriv k correction) := by
  have hre : iteratedDeriv k (fun x : ℝ ↦ (modelCorrection (x : ℂ)).re)
      = fun x : ℝ ↦ (iteratedDeriv k modelCorrection (x : ℂ)).re :=
    funext fun x ↦ differentiable_modelCorrection.iteratedDeriv_re_of_complex k x
  rw [correction_eq_re, hre]
  exact fun x ↦
    ((differentiable_iteratedDeriv_modelCorrection k _).hasDerivAt.real_of_complex).differentiableAt

/-- `Ψ` is differentiable. -/
theorem differentiable_correction : Differentiable ℝ correction := by
  simpa using differentiable_iteratedDeriv_correction 0

private theorem hasDerivAt_iteratedDeriv_correction (k : ℕ) (p : ℝ) :
    HasDerivAt (iteratedDeriv k correction) (iteratedDeriv (k + 1) correction p) p := by
  rw [iteratedDeriv_succ]
  exact (differentiable_iteratedDeriv_correction k p).hasDerivAt

private theorem hasDerivAt_correction (p : ℝ) :
    HasDerivAt correction (iteratedDeriv 1 correction p) p := by
  simpa only [iteratedDeriv_zero] using hasDerivAt_iteratedDeriv_correction 0 p

private theorem hasDerivAt_deriv_correction (p : ℝ) :
    HasDerivAt (iteratedDeriv 1 correction) (iteratedDeriv 2 correction p) p :=
  hasDerivAt_iteratedDeriv_correction 1 p

/-- The angle `φ = 2π(p² − p − 1/16)` and its derivative, as a `HasDerivAt`. -/
private theorem hasDerivAt_phase (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ 2 * π * (x ^ 2 - x - 1 / 16)) (2 * π * (2 * p - 1)) p := by
  have : HasDerivAt (fun x : ℝ ↦ x ^ 2 - x - 1 / 16) (2 * p - 1) p := by
    simpa using ((hasDerivAt_pow 2 p).sub (hasDerivAt_id p)).sub_const (1 / 16)
  simpa using this.const_mul (2 * π)

private theorem hasDerivAt_cos_two_pi (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x)) (-Real.sin (2 * π * p) * (2 * π)) p := by
  simpa using (((hasDerivAt_id p).const_mul (2 * π)).cos)

private theorem hasDerivAt_sin_two_pi (p : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.sin (2 * π * x)) (Real.cos (2 * π * p) * (2 * π)) p := by
  simpa using (((hasDerivAt_id p).const_mul (2 * π)).sin)

/-! ### The product-form identities

`C·Ψ⁽ᵏ⁾ = …`, obtained by differentiating `cos_mul_correction` repeatedly. No division and no
`C ≠ 0` hypothesis, so each is a plain product-rule step; the divided forms the certificate
builder renames onto are one `eq_div_iff` away. -/

/-- `C·Ψ' = R₁ − C'·Ψ`. -/
theorem cos_mul_iteratedDeriv_one (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 1 correction p
      = -Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1))
        - -Real.sin (2 * π * p) * (2 * π) * correction p := by
  have hprod : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * correction x)
      (-Real.sin (2 * π * p) * (2 * π) * correction p
        + Real.cos (2 * π * p) * iteratedDeriv 1 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_correction p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * correction x)
      = fun x : ℝ ↦ Real.cos (2 * π * (x ^ 2 - x - 1 / 16)) := funext cos_mul_correction
  rw [hfun] at hprod
  have hu := hprod.unique (hasDerivAt_phase p).cos
  linarith [hu]

/-- `C·Ψ'' = R₂ − 2C'·Ψ' − C''·Ψ`. -/
theorem cos_mul_iteratedDeriv_two (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 2 correction p
      = (-Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * ((2 * π * (2 * p - 1)) * (2 * π * (2 * p - 1)))
          - Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (4 * π))
        - 2 * (-Real.sin (2 * π * p) * (2 * π)) * iteratedDeriv 1 correction p
        - -Real.cos (2 * π * p) * ((2 * π) * (2 * π)) * correction p := by
  have hL : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 1 correction x)
      (-Real.sin (2 * π * p) * (2 * π) * iteratedDeriv 1 correction p
        + Real.cos (2 * π * p) * iteratedDeriv 2 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_deriv_correction p)
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * π * (2 * x - 1)) (2 * π * 2) p := by
    simpa using (((hasDerivAt_id p).const_mul 2).sub_const 1).const_mul (2 * π)
  have hA := (((hasDerivAt_phase p).sin).neg).mul hlin
  have hB := ((hasDerivAt_sin_two_pi p).neg.mul_const (2 * π)).mul (hasDerivAt_correction p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 1 correction x)
      = fun x : ℝ ↦ -Real.sin (2 * π * (x ^ 2 - x - 1 / 16)) * (2 * π * (2 * x - 1))
          - -Real.sin (2 * π * x) * (2 * π) * correction x :=
    funext cos_mul_iteratedDeriv_one
  rw [hfun] at hL
  have hu := hL.unique (hA.sub hB)
  simp only [Pi.neg_apply] at hu
  linear_combination hu

/-- `C · Ψ⁗₃ = R₃ − 3C'·Ψ'' − 3C''·Ψ' − C'''·Ψ`, the third-derivative product form. -/
theorem cos_mul_iteratedDeriv_three (p : ℝ) :
    Real.cos (2 * π * p) * iteratedDeriv 3 correction p
      = (-(-Real.sin (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1)))
            * ((2 * π * (2 * p - 1)) * (2 * π * (2 * p - 1)))
          + -Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * (2 * π * (2 * p - 1)) * (2 * π * 2))
          - Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) * (2 * π * (2 * p - 1)) * (4 * π))
        - 2 * (-(Real.cos (2 * π * p) * (2 * π)) * (2 * π)) * iteratedDeriv 1 correction p
        - 3 * (-Real.sin (2 * π * p) * (2 * π)) * iteratedDeriv 2 correction p
        - (-(-Real.sin (2 * π * p) * (2 * π)) * ((2 * π) * (2 * π)) * correction p
            + -Real.cos (2 * π * p) * ((2 * π) * (2 * π)) * iteratedDeriv 1 correction p) := by
  have hphi := hasDerivAt_phase p
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * π * (2 * x - 1)) (2 * π * 2) p := by
    simpa using (((hasDerivAt_id p).const_mul 2).sub_const 1).const_mul (2 * π)
  have hsq : HasDerivAt (fun x : ℝ ↦ (2 * π * (2 * x - 1)) * (2 * π * (2 * x - 1)))
      (2 * π * 2 * (2 * π * (2 * p - 1)) + 2 * π * (2 * p - 1) * (2 * π * 2)) p :=
    hlin.mul hlin
  have hA := ((hphi.cos).neg).mul hsq
  have hB := (hphi.sin).mul_const (4 * π)
  have hD := (((hasDerivAt_sin_two_pi p).neg.mul_const (2 * π)).const_mul 2).mul
    (hasDerivAt_deriv_correction p)
  have hE := (((hasDerivAt_cos_two_pi p).neg).mul_const (((2 * π) * (2 * π)))).mul
    (hasDerivAt_correction p)
  have hL : HasDerivAt (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 2 correction x)
      (-Real.sin (2 * π * p) * (2 * π) * iteratedDeriv 2 correction p
        + Real.cos (2 * π * p) * iteratedDeriv 3 correction p) p :=
    (hasDerivAt_cos_two_pi p).mul (hasDerivAt_iteratedDeriv_correction 2 p)
  have hfun : (fun x : ℝ ↦ Real.cos (2 * π * x) * iteratedDeriv 2 correction x)
      = fun x : ℝ ↦
          (-Real.cos (2 * π * (x ^ 2 - x - 1 / 16))
                * ((2 * π * (2 * x - 1)) * (2 * π * (2 * x - 1)))
              - Real.sin (2 * π * (x ^ 2 - x - 1 / 16)) * (4 * π))
            - 2 * (-Real.sin (2 * π * x) * (2 * π)) * iteratedDeriv 1 correction x
            - -Real.cos (2 * π * x) * ((2 * π) * (2 * π)) * correction x :=
    funext cos_mul_iteratedDeriv_two
  rw [hfun] at hL
  have hu := hL.unique (((hA.sub hB).sub hD).sub hE)
  simp only [Pi.neg_apply] at hu
  linear_combination hu

end Zeta.RiemannSiegel
