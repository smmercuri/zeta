/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Analysis.Complex.Arg
public import Zeta.Analysis.SpecialFunctions.Arctan
public import Zeta.Gamma.DigammaStirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Growth of `|Γ|` on vertical lines

The two-sided vertical-strip growth bound for the complex Gamma function (`sec:gs_growth`):
for fixed `0 < a ≤ b` there are `0 < c₁ ≤ c₂` with
`c₁·|t|^{σ-1/2}·e^{-(π/2)|t|} ≤ ‖Γ(σ + it)‖ ≤ c₂·|t|^{σ-1/2}·e^{-(π/2)|t|}` for `σ ∈ [a, b]`,
`|t| ≥ 1`, together with the branch-free derivative identity and closed-form integrals it rests on.

## Main results

* `Complex.hasDerivAt_log_norm`, `Complex.hasDerivAt_log_norm_Gamma_comp`,
  `Complex.hasDerivAt_log_norm_Gamma_vertical` (`lem:gs_deriv_logabs`):
  `d/dt log‖Γ(σ + it)‖ = -Im ψ(σ + it)`.
* `Complex.integral_im_log_add_ofReal_mul_I` (`lem:gs_arg_integral`):
  `∫₀ᵗ Im Log(σ + iτ) dτ = t·arctan(t/σ) - (σ/2)·log(1 + t²/σ²)`.
* `Complex.continuousAt_digamma`: continuity of `ψ` on `{Re > 0}`.
* `Complex.log_norm_Gamma_remainder_le`: the uniform remainder bound with explicit constants.
* `Complex.norm_Gamma_vertical_le` (`thm:gs_Gamma_growth`): the growth bound.
-/
@[expose] public section


open MeasureTheory
open scoped Topology

namespace Complex
open Complex.Stirling

/-- Derivative of `u ↦ arctan (u / σ)`. -/
private theorem hasDerivAt_arctan_div (σ u : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan (u / σ)) (1 / (1 + (u / σ) ^ 2) * (1 / σ)) u := by
  have hd1 : HasDerivAt (fun u : ℝ ↦ u / σ) (1 / σ) u := (hasDerivAt_id u).div_const σ
  simpa only [Function.comp_def] using (Real.hasDerivAt_arctan (u / σ)).comp u hd1

/-- Derivative of `u ↦ log (σ² + u²)` for `σ > 0`. -/
private theorem hasDerivAt_log_sq_add {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.log (σ ^ 2 + u ^ 2)) ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) u := by
  have hpos : (0 : ℝ) < σ ^ 2 + u ^ 2 := by positivity
  have hin : HasDerivAt (fun u : ℝ ↦ σ ^ 2 + u ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).const_add (σ ^ 2)
  simpa only [Function.comp_def] using (Real.hasDerivAt_log hpos.ne').comp u hin

/-- The logarithmic identity `log(1 + t²/σ²) = log(σ² + t²) - log(σ²)` for `σ > 0`. -/
private theorem log_one_add_sq_div {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Real.log (1 + t ^ 2 / σ ^ 2) = Real.log (σ ^ 2 + t ^ 2) - Real.log (σ ^ 2) := by
  have hσne : σ ≠ 0 := hσ.ne'
  rw [show (1 + t ^ 2 / σ ^ 2) = (σ ^ 2 + t ^ 2) / σ ^ 2 by field_simp,
    Real.log_div (by positivity) (by positivity)]

/-- Branch-free derivative of `log‖G‖`: for a complex-valued path `G : ℝ → ℂ` differentiable
at `x` with `G x ≠ 0`, the real function `t ↦ log‖G t‖` is differentiable at `x` with derivative
`Re(G'(x) / G x)`. -/
theorem hasDerivAt_log_norm {G : ℝ → ℂ} {g' : ℂ} {x : ℝ}
    (hG : HasDerivAt G g' x) (hne : G x ≠ 0) :
    HasDerivAt (fun t ↦ Real.log ‖G t‖) (g' / G x).re x := by
  have hpos : (0 : ℝ) < ‖G x‖ ^ 2 := by positivity
  have hnsq := HasDerivAt.norm_sq hG
  have hlog0 := (Real.hasDerivAt_log hpos.ne').comp x hnsq
  have hfun : (fun t ↦ Real.log ‖G t‖) = fun t ↦ (2 : ℝ)⁻¹ * Real.log (‖G t‖ ^ 2) := by
    funext t; rw [Real.log_pow]; push_cast; ring
  rw [hfun]
  have hval : (g' / G x).re
      = (2 : ℝ)⁻¹ * ((‖G x‖ ^ 2)⁻¹ * (2 * inner ℝ (G x) g')) := by
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.div_re, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [hval]
  exact hlog0.const_mul (2 : ℝ)⁻¹

/-- Chain rule for `log‖Γ ∘ φ‖`: for a complex path `φ : ℝ → ℂ` differentiable at `x` whose
value `φ x` lies in the right half-plane, `d/dx log‖Γ(φ x)‖ = Re (φ'(x) · ψ(φ x))` with
`ψ = Complex.digamma`. -/
theorem hasDerivAt_log_norm_Gamma_comp {φ : ℝ → ℂ} {φ' : ℂ} {x : ℝ}
    (hφ : HasDerivAt φ φ' x) (hre : 0 < (φ x).re) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖Complex.Gamma (φ u)‖)
      (φ' * Complex.digamma (φ x)).re x := by
  have hG : HasDerivAt (fun u : ℝ ↦ Complex.Gamma (φ u)) (deriv Complex.Gamma (φ x) * φ') x := by
    simpa only [Function.comp_def] using
      (differentiableAt_Gamma_of_re_pos hre).hasDerivAt.comp x hφ
  convert hasDerivAt_log_norm hG (Complex.Gamma_ne_zero_of_re_pos hre) using 2
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp

/-- Vertical derivative of `log|Γ|` (`lem:gs_deriv_logabs`): for `σ > 0` and `t ∈ ℝ`,
`d/dt log‖Γ(σ + i t)‖ = -Im ψ(σ + i t)`, with `ψ = Complex.digamma`. -/
theorem hasDerivAt_log_norm_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun τ : ℝ ↦ Real.log ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖)
      (-(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im) t := by
  have hpath : HasDerivAt (fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) Complex.I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add (σ : ℂ)
  simpa [Complex.I_mul_re] using hasDerivAt_log_norm_Gamma_comp hpath (by simp [hσ])

/-- The integrated argument (`lem:gs_arg_integral`): for `σ > 0` and any `t`,
`∫₀ᵗ Im Log(σ + i τ) dτ = t·arctan(t/σ) - (σ/2)·log(1 + t²/σ²)`. -/
theorem integral_im_log_add_ofReal_mul_I {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
      = t * Real.arctan (t / σ) - σ / 2 * Real.log (1 + t ^ 2 / σ ^ 2) := by
  have hσne : σ ≠ 0 := hσ.ne'
  -- The integrand is `arg(σ + iτ) = arctan(τ/σ)`.
  have harg : ∀ τ : ℝ, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im = Real.arctan (τ / σ) := by
    intro τ
    have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
    rw [Complex.log_im, Complex.arg_eq_arctan (by rw [hre]; exact hσ), hre, him]
  -- An explicit antiderivative of `u ↦ arctan(u/σ)`.
  have hF : ∀ u : ℝ, HasDerivAt
      (fun u ↦ u * Real.arctan (u / σ) - σ / 2 * Real.log (σ ^ 2 + u ^ 2))
      (Real.arctan (u / σ)) u := by
    intro u
    have hp1 : HasDerivAt (fun u ↦ u * Real.arctan (u / σ))
        (1 * Real.arctan (u / σ) + u * (1 / (1 + (u / σ) ^ 2) * (1 / σ))) u :=
      (hasDerivAt_id u).mul (hasDerivAt_arctan_div σ u)
    have hp2 : HasDerivAt (fun u ↦ σ / 2 * Real.log (σ ^ 2 + u ^ 2))
        (σ / 2 * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u))) u := (hasDerivAt_log_sq_add hσ u).const_mul (σ / 2)
    have hval : 1 * Real.arctan (u / σ) + u * (1 / (1 + (u / σ) ^ 2) * (1 / σ))
          - σ / 2 * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) = Real.arctan (u / σ) := by
      have hne1 : (1 + (u / σ) ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    exact hval ▸ hp1.sub hp2
  have hcont : IntervalIntegrable (fun τ ↦ Real.arctan (τ / σ)) volume 0 t :=
    (Real.continuous_arctan.comp (continuous_id.div_const σ)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_congr (g := fun τ ↦ Real.arctan (τ / σ)) (fun τ _ ↦ harg τ),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u) hcont]
  rw [log_one_add_sq_div hσ]
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  ring

/-- Continuity of the digamma function on the right half-plane: for `Re z > 0`, `ψ = digamma`
is continuous at `z`. -/
theorem continuousAt_digamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt Complex.digamma z :=
  (differentiableAt_digamma hz).continuousAt

/-- The integrand `τ ↦ Im ψ(σ + i τ)` is continuous for `σ > 0`. -/
private theorem continuous_im_digamma_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    (Complex.continuous_im.continuousAt.comp
      (continuousAt_digamma (z := (σ : ℂ) + (τ : ℂ) * Complex.I) (by simpa using hσ))).comp
        (f := fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) (by fun_prop)

/-- The imaginary part of `(2(σ + i τ))⁻¹`, in closed form. -/
private theorem inv_two_z_im {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im = -τ / (2 * (σ ^ 2 + τ ^ 2)) := by
  simp [Complex.inv_im, Complex.normSq_apply]; field_simp [hσ.ne']

/-- The vertical integral of `Im (2(σ + iτ))⁻¹` in closed form: `-(1/4) log(1 + t²/σ²)`. -/
private theorem integral_inv_two_z_im {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im)
      = -(1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) := by
  rw [intervalIntegral.integral_congr (g := fun τ ↦ -τ / (2 * (σ ^ 2 + τ ^ 2)))
    (fun τ _ ↦ inv_two_z_im hσ τ)]
  have hH : ∀ u : ℝ, HasDerivAt (fun u ↦ -(1 / 4) * Real.log (σ ^ 2 + u ^ 2))
      (-u / (2 * (σ ^ 2 + u ^ 2))) u := by
    intro u
    have hval : -(1 / 4) * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) = -u / (2 * (σ ^ 2 + u ^ 2)) := by
      have : (σ ^ 2 + u ^ 2) ≠ 0 := by positivity
      field_simp; ring
    exact hval ▸ (hasDerivAt_log_sq_add hσ u).const_mul (-(1 / 4))
  have hcont : IntervalIntegrable (fun τ ↦ -τ / (2 * (σ ^ 2 + τ ^ 2))) volume 0 t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hH u) hcont]
  rw [log_one_add_sq_div hσ]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  ring

/-- The vertical integral of `(σ² + τ²)⁻¹` in closed form: `arctan(t/σ)/σ`. -/
private theorem integral_inv_sq_add {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, (σ ^ 2 + τ ^ 2)⁻¹) = Real.arctan (t / σ) / σ := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u ↦ Real.arctan (u / σ) / σ) ((σ ^ 2 + u ^ 2)⁻¹) u := by
    intro u
    have hval : 1 / (1 + (u / σ) ^ 2) * (1 / σ) / σ = (σ ^ 2 + u ^ 2)⁻¹ := by
      have hσne : σ ≠ 0 := hσ.ne'
      have : (1 + (u / σ) ^ 2) ≠ 0 := by positivity
      field_simp
    exact hval ▸ (hasDerivAt_arctan_div σ u).div_const σ
  have hcont : IntervalIntegrable (fun τ ↦ (σ ^ 2 + τ ^ 2)⁻¹) volume 0 t := by
    apply Continuous.intervalIntegrable
    exact Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u) hcont]
  simp only [zero_div, Real.arctan_zero, sub_zero]

/-- `Im E(σ + iτ)`, the imaginary part of the digamma Stirling error
`E(s) = ψ(s) - Log s + (2s)⁻¹` (`cor:gs_digamma_first_order`), restricted to the vertical line
`s = σ + iτ`. -/
private noncomputable def imDigammaError (σ τ : ℝ) : ℝ :=
  (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I) - Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)
    + (2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im

/-- The integrand `τ ↦ Im Log(σ + i τ)` is continuous for `σ > 0`. -/
private theorem continuous_im_log_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    Complex.continuous_im.continuousAt.comp
      ((by fun_prop : ContinuousAt (fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) τ).clog
        (Or.inl (by simpa using hσ)))

/-- The integrand `τ ↦ Im (2(σ + i τ))⁻¹` is continuous for `σ > 0`. -/
private theorem continuous_im_inv_two_z {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    Complex.continuous_im.continuousAt.comp
      ((by fun_prop : ContinuousAt (fun τ : ℝ ↦ 2 * ((σ : ℂ) + (τ : ℂ) * Complex.I)) τ).inv₀
        (mul_ne_zero two_ne_zero (Complex.ne_zero_of_re_pos (by simpa using hσ))))

/-- The integrand `τ ↦ Im E(σ + i τ)` is continuous for `σ > 0`. -/
private theorem continuous_imDigammaError {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ imDigammaError σ τ) := by
  unfold imDigammaError; simp only [Complex.add_im, Complex.sub_im]
  exact ((continuous_im_digamma_vertical hσ).sub (continuous_im_log_vertical hσ)).add
    (continuous_im_inv_two_z hσ)

/-- Exact vertical integral identity for `log|Γ|`: for `σ > 0`,
`log‖Γ(σ + it)‖ = log‖Γ(σ)‖ - t·arctan(t/σ) + (σ/2 - 1/4)·log(1 + t²/σ²) - ∫₀ᵗ Im E(σ + iτ) dτ`. -/
private theorem log_norm_Gamma_vertical_eq {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = Real.log ‖Complex.Gamma (σ : ℂ)‖ - t * Real.arctan (t / σ)
        + (σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2)
        - ∫ τ in (0 : ℝ)..t, imDigammaError σ τ := by
  have ii_ψ : IntervalIntegrable
      (fun τ : ℝ ↦ (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) volume 0 t :=
    (continuous_im_digamma_vertical hσ).intervalIntegrable 0 t
  have ii_log : IntervalIntegrable
      (fun τ : ℝ ↦ (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) volume 0 t :=
    (continuous_im_log_vertical hσ).intervalIntegrable 0 t
  have ii_inv : IntervalIntegrable
      (fun τ : ℝ ↦ ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im) volume 0 t :=
    (continuous_im_inv_two_z hσ).intervalIntegrable 0 t
  -- FTC on `lem:gs_deriv_logabs`: `-∫₀ᵗ Im ψ = log‖Γ(σ + it)‖ - log‖Γ(σ)‖`
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ ↦ Real.log ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖)
    (fun x _ ↦ hasDerivAt_log_norm_Gamma_vertical hσ x) ii_ψ.neg
  rw [intervalIntegral.integral_neg, Complex.ofReal_zero, zero_mul, add_zero] at hftc
  -- `∫ Im E = ∫ Im ψ - ∫ Im Log + ∫ Im (2z)⁻¹`, the last two in closed form
  have hE : (∫ τ in (0 : ℝ)..t, imDigammaError σ τ)
      = ((∫ τ in (0 : ℝ)..t, (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
          - ∫ τ in (0 : ℝ)..t, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
        + ∫ τ in (0 : ℝ)..t, ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im := by
    rw [← intervalIntegral.integral_sub ii_ψ ii_log,
      ← intervalIntegral.integral_add (ii_ψ.sub ii_log) ii_inv]
    exact intervalIntegral.integral_congr fun τ _ ↦ by
      simp only [imDigammaError, Complex.add_im, Complex.sub_im]
  rw [integral_im_log_add_ofReal_mul_I hσ, integral_inv_two_z_im hσ] at hE
  linarith [hftc, hE]

/-- `σ ↦ log‖Γ(σ)‖` is bounded on the compact interval `[a, b]` (with `a > 0`). -/
private theorem log_norm_Gamma_bounded {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, ∀ σ ∈ Set.Icc a b, |Real.log ‖Complex.Gamma (σ : ℂ)‖| ≤ M := by
  have hcontOn : ContinuousOn (fun σ : ℝ ↦ Real.log ‖Complex.Gamma (σ : ℂ)‖) (Set.Icc a b) := by
    intro σ hσ
    have hsre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using lt_of_lt_of_le ha hσ.1
    have hΓc : ContinuousAt (fun σ : ℝ ↦ Complex.Gamma (σ : ℂ)) σ :=
      (differentiableAt_Gamma_of_re_pos hsre).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    exact ((hΓc.norm).log
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hsre))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  exact ⟨M, fun σ hσ ↦ by simpa [Real.norm_eq_abs] using hM σ hσ⟩

/-- The cancellation `t(π/2 - arctan(t/σ))` lies in `[0, b]` for `0 < σ ≤ b`, `t ≥ 1`. -/
private theorem pi_div_two_sub_arctan_bound {b σ t : ℝ} (hσ : 0 < σ) (hσb : σ ≤ b) (ht : 1 ≤ t) :
    0 ≤ Real.pi / 2 * t - t * Real.arctan (t / σ) ∧
    Real.pi / 2 * t - t * Real.arctan (t / σ) ≤ b := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have harc_lt : Real.arctan (t / σ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  refine ⟨by nlinarith [harc_lt, htpos], ?_⟩
  have hxpos : 0 < t / σ := by positivity
  have hinv : Real.arctan (σ / t) = Real.pi / 2 - Real.arctan (t / σ) := by
    have := Real.arctan_inv_of_pos hxpos
    rwa [inv_div] at this
  have hB : Real.pi / 2 * t - t * Real.arctan (t / σ) = t * Real.arctan (σ / t) := by
    rw [hinv]; ring
  rw [hB]
  have h1 : Real.arctan (σ / t) ≤ σ / t := Real.arctan_le_self (by positivity)
  have h2 : t * Real.arctan (σ / t) ≤ t * (σ / t) := mul_le_mul_of_nonneg_left h1 htpos.le
  have h3 : t * (σ / t) = σ := by field_simp
  linarith [h2, h3, hσb]

/-- The combined logarithmic term `(σ/2 - 1/4)·log(1 + t²/σ²) - (σ - 1/2)·log t` is bounded
uniformly for `σ ∈ [a, b]`, `t ≥ 1`. -/
private theorem abs_log_growth_term_le {a b σ t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hσa : a ≤ σ) (hσb : σ ≤ b) (ht : 1 ≤ t) :
    |(σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) - (σ - 1 / 2) * Real.log t|
      ≤ (b / 2 + 1 / 4) * (|Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)|) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- `1 + t²/σ² = t²·y` with `y = 1/t² + 1/σ²`, so the `log t` terms cancel exactly.
  set y := 1 / t ^ 2 + 1 / σ ^ 2 with hy
  have hLid : Real.log (1 + t ^ 2 / σ ^ 2) - 2 * Real.log t = Real.log y := by
    rw [show (1 + t ^ 2 / σ ^ 2) = t ^ 2 * y by rw [hy]; field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [show (σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) - (σ - 1 / 2) * Real.log t
      = (σ / 2 - 1 / 4) * Real.log y by
    rw [show (σ - 1 / 2) = 2 * (σ / 2 - 1 / 4) by ring, ← hLid]; ring, abs_mul]
  -- Both factors are bounded: the coefficient by `b/2 + 1/4`, and `y ∈ [1/b², 1 + 1/a²]`.
  have hyU : y ≤ 1 + 1 / a ^ 2 := by
    have h1t : 1 / t ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [ht]
    have : 1 / σ ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith [hσa])
    rw [hy]; linarith
  have hyL : 1 / b ^ 2 ≤ y := by
    have : 1 / b ^ 2 ≤ 1 / σ ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith [hσb])
    have : (0 : ℝ) < 1 / t ^ 2 := by positivity
    rw [hy]; linarith
  have hlogbound : |Real.log y| ≤ |Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)| := by
    have hup := Real.log_le_log (show (0 : ℝ) < y by rw [hy]; positivity) hyU
    have hlo := Real.log_le_log (show (0 : ℝ) < 1 / b ^ 2 by positivity) hyL
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (1 / b ^ 2)), abs_nonneg (Real.log (1 + 1 / a ^ 2))]
    · linarith [le_abs_self (Real.log (1 + 1 / a ^ 2)), abs_nonneg (Real.log (1 / b ^ 2))]
  exact mul_le_mul (by rw [abs_le]; constructor <;> nlinarith) hlogbound (abs_nonneg _)
    (by linarith)

/-- Bound on the error integral: for `σ ≥ a > 0` and `t ≥ 0`, given the first-order digamma
bound `‖E(s)‖ ≤ C₀‖s‖⁻²`, one has `|∫₀ᵗ Im E(σ + iτ) dτ| ≤ C₀·π/(2a)`, uniformly in `t`. -/
private theorem abs_integral_imDigammaError_le {a : ℝ} (ha : 0 < a) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hbound : ∀ s : ℂ, a ≤ s.re →
      ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ C₀ * ‖s‖ ^ (-(2 : ℤ)))
    {σ : ℝ} (hσa : a ≤ σ) {t : ℝ} (ht : 0 ≤ t) :
    |∫ τ in (0 : ℝ)..t, imDigammaError σ τ| ≤ C₀ * Real.pi / (2 * a) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  -- pointwise: `|Im E| ≤ ‖E‖ ≤ C₀‖σ + iτ‖⁻² = C₀ (σ² + τ²)⁻¹`
  have hpt : ∀ τ : ℝ, |imDigammaError σ τ| ≤ C₀ * (σ ^ 2 + τ ^ 2)⁻¹ := fun τ ↦ by
    have hsq : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ (2 : ℕ) = σ ^ 2 + τ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have h2 := hbound ((σ : ℂ) + (τ : ℂ) * Complex.I) (by simpa using hσa)
    rw [show ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ (-(2 : ℤ)) = (σ ^ 2 + τ ^ 2)⁻¹ by
      rw [zpow_neg, ← hsq]; norm_cast] at h2
    exact le_trans (Complex.abs_im_le_norm _) h2
  have iiE : IntervalIntegrable (fun τ ↦ |imDigammaError σ τ|) volume 0 t :=
    ((continuous_imDigammaError hσ).abs).intervalIntegrable 0 t
  have iiB : IntervalIntegrable (fun τ ↦ C₀ * (σ ^ 2 + τ ^ 2)⁻¹) volume 0 t :=
    (Continuous.mul continuous_const
      (Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity))).intervalIntegrable 0 t
  have harc : Real.arctan (t / σ) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
  calc |∫ τ in (0 : ℝ)..t, imDigammaError σ τ|
      ≤ ∫ τ in (0 : ℝ)..t, |imDigammaError σ τ| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ τ in (0 : ℝ)..t, C₀ * (σ ^ 2 + τ ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on ht iiE iiB (fun x _ ↦ hpt x)
    _ = C₀ * (Real.arctan (t / σ) / σ) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sq_add hσ]
    _ ≤ C₀ * (Real.pi / 2 / a) := mul_le_mul_of_nonneg_left (by gcongr) hC₀.le
    _ = C₀ * Real.pi / (2 * a) := by rw [div_div]; ring

/-- Explicit uniform two-sided bound on the remainder `log‖Γ(σ + it)‖ - ((σ - 1/2)·log t -
(π/2)·t)`, in terms of given constants `M` (a bound on `|log‖Γ(σ)‖|` over `[a, b]`) and `C₀` (the
digamma-remainder constant). -/
theorem log_norm_Gamma_remainder_le {a b M C₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM : ∀ σ ∈ Set.Icc a b, |Real.log ‖Complex.Gamma (σ : ℂ)‖| ≤ M) (hC₀ : 0 < C₀)
    (hCb : ∀ s : ℂ, a ≤ s.re →
      ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ C₀ * ‖s‖ ^ (-(2 : ℤ)))
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) {t : ℝ} (ht : 1 ≤ t) :
    |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)|
      ≤ M + b + (b / 2 + 1 / 4) * (|Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)|)
        + C₀ * Real.pi / (2 * a) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  rw [log_norm_Gamma_vertical_eq hσ]
  have hA := abs_le.mp (hM σ ⟨hσa, hσb⟩)
  obtain ⟨hB0, hBb⟩ := pi_div_two_sub_arctan_bound hσ hσb ht
  have hC := abs_le.mp (abs_log_growth_term_le ha hab hσa hσb ht)
  have hD := abs_le.mp (abs_integral_imDigammaError_le ha C₀ hC₀ hCb hσa ht0)
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith [hA.1, hA.2, hB0, hBb, hC.1, hC.2, hD.1, hD.2]

/-- Uniform two-sided bound on the remainder `log‖Γ(σ + it)‖ - ((σ - 1/2)·log t - (π/2)·t)`
for `σ ∈ [a, b]`, `t ≥ 1`. -/
private theorem log_norm_Gamma_remainder_bounded {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ t →
      |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)| ≤ K := by
  obtain ⟨M, hM⟩ := log_norm_Gamma_bounded (a := a) (b := b) ha
  have hC₀ : (0 : ℝ) < 1 / 12 + 3 / (2 * Real.pi ^ 2 * a) := by positivity
  have hCb := fun s has ↦ Complex.Stirling.norm_digamma_sub_log_le' ha s has
  exact ⟨_, fun σ hσa hσb t ht ↦ log_norm_Gamma_remainder_le ha hab hM hC₀ hCb hσa hσb ht⟩

/-- The `τ ≥ 1` half of `norm_Gamma_vertical_le`, with `c₁ = e^{-K}`, `c₂ = e^{K}` for `K` the
additive constant of the uniform log-remainder bound. -/
private theorem norm_Gamma_vertical_le_of_one_le {a b K : ℝ} (ha : 0 < a)
    (hK : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ t →
      |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)| ≤ K)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) {τ : ℝ} (hτ : 1 ≤ τ) :
    Real.exp (-K) * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ)
        ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ Real.exp K * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ
  have hsre : (0 : ℝ) < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simp [hσ]
  have hG : 0 < ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hsre)
  set G := ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
  set P := τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  have hlogP : Real.log P = (σ - 1 / 2) * Real.log τ - Real.pi / 2 * τ := by
    rw [hPdef, Real.log_mul (by positivity) (by positivity), Real.log_rpow hτ0, Real.log_exp]
    ring
  have hbnd := hK σ hσa hσb τ hτ
  rw [← hlogP, ← Real.log_div hG.ne' hP.ne'] at hbnd
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbnd
  -- `|log (G/P)| ≤ K`, so `e^{-K} ≤ G/P ≤ e^K`; clear the denominator `P > 0`.
  have heq : Real.exp (Real.log (G / P)) = G / P := Real.exp_log (div_pos hG hP)
  rw [show Real.exp (-K) * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) = Real.exp (-K) * P by
      rw [hPdef]; ring,
    show Real.exp K * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) = Real.exp K * P by
      rw [hPdef]; ring]
  exact ⟨(le_div_iff₀ hP).mp (heq ▸ Real.exp_le_exp.mpr hlo),
    (div_le_iff₀ hP).mp (heq ▸ Real.exp_le_exp.mpr hhi)⟩

/-- Vertical-strip growth bound for `Γ` (`thm:gs_Gamma_growth`). Fix `0 < a ≤ b`. There are
constants `0 < c₁ ≤ c₂`, depending only on `a, b`, such that for all `σ ∈ [a, b]` and all `t` with
`|t| ≥ 1`,
`c₁·|t|^{σ-1/2}·e^{-(π/2)|t|} ≤ ‖Γ(σ + it)‖ ≤ c₂·|t|^{σ-1/2}·e^{-(π/2)|t|}`. -/
theorem norm_Gamma_vertical_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ |t| →
      c₁ * |t| ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|)
        ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ c₂ * |t| ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|) := by
  obtain ⟨K, hK⟩ := log_norm_Gamma_remainder_bounded ha hab
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK a le_rfl hab 1 le_rfl)
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _,
    Real.exp_le_exp.mpr (by linarith), fun σ hσa hσb t ht ↦ ?_⟩
  -- Conjugate symmetry `Γ(z̄) = Γ(z)‾` replaces `t` by `|t|`, reducing to the `t ≥ 1` case.
  have hnorm : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖Complex.Gamma ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ := by
    rcases abs_choice t with h | h <;> rw [h]
    rw [show ((σ : ℂ) + (t : ℂ) * Complex.I)
      = starRingEnd ℂ ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) by simp,
      Complex.Gamma_conj, Complex.norm_conj]
  rw [hnorm]
  exact norm_Gamma_vertical_le_of_one_le ha hK hσa hσb ht

end Complex
