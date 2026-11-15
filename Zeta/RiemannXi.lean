/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Zeta.Gamma.HalfPlane

/-!
# The Riemann ξ function

The entire completion `ξ(s) = ½ s (s - 1) Λ(s)` of `ζ`, with `Λ = completedRiemannZeta`.
It is defined through the entire normalisation `Λ₀ = completedRiemannZeta₀`, since the literal
expression does not extend continuously through Lean's junk values at the poles `s = 0, 1`.

## Main definitions

- `riemannXi`: the Riemann ξ function.

## Main results

- `riemannXi_eq_mul_completedRiemannZeta`: away from `s = 0, 1`, `ξ(s) = ½ s (s - 1) Λ(s)`.
- `differentiable_riemannXi`, `analyticOnNhd_riemannXi`: `ξ` is entire.
- `riemannXi_one_sub`: the functional equation `ξ(1 - s) = ξ(s)`.
- `riemannXi_conj`: the conjugation symmetry `ξ(conj s) = conj (ξ s)`.
- `riemannXi_eq_zero_iff`: on the critical strip `0 < Re s < 1`, `ξ(s) = 0 ↔ ζ(s) = 0`.
- `meromorphicOrderAt_riemannXi_eq_riemannZeta`: on the critical strip the meromorphic orders
  of `ξ` and `ζ` agree.
- `Complex.analyticAt_Gammaℝ`, `completedRiemannZeta₀_conj`: conjugation
  symmetry and analyticity of the underlying completed-zeta objects.
-/
@[expose] public section


open Complex

namespace Complex

/-- The real Gamma factor `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` is analytic on the right half-plane
`Re s > 0`. -/
theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) (Complex.isOpen_re_gt 0) s hs
  have hz2 : 0 < (z / 2).re := by
    have hz0 : (0 : ℝ) < z.re := hz
    rw [div_ofNat_re]; linarith
  exact (DifferentiableAt.const_cpow (differentiableAt_id.neg.div_const 2)
    (Or.inl (by exact_mod_cast Real.pi_ne_zero)) |>.mul
      ((Complex.differentiableAt_Gamma_of_re_pos hz2).comp z
        (differentiableAt_id.div_const 2))).differentiableWithinAt

/-- The real Gamma factor `Γ_ℝ` is non-vanishing off the real axis. -/
theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, rfl⟩
  simp at h

end Complex

/-- The completed zeta factors as `Λ(s) = ζ(s) Γ_ℝ(s)` wherever `s ≠ 0` and `Γ_ℝ(s) ≠ 0`. -/
private theorem completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ {s : ℂ} (hs : s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs, div_mul_cancel₀ _ hΓ]

/-- Conjugation symmetry of the entire completed zeta `Λ₀`, in the form
`conj (Λ₀(conj s)) = Λ₀(s)`. -/
private theorem conj_completedRiemannZeta₀_conj (s : ℂ) :
    starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ s)) = completedRiemannZeta₀ s := by
  have hd : Differentiable ℂ fun z ↦ starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ z)) :=
    fun z ↦ by
      simpa [Function.comp_def] using
        (differentiable_completedZeta₀ (starRingEnd ℂ z)).conj_conj
  refine (hd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ
    (Set.mem_univ 2) ?_ (Set.mem_univ s)
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Complex.re ⁻¹' Set.Ioi 1,
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num), fun t ht ↦ ?_⟩
  have ht : 1 < t.re := ht
  have htc : 1 < (starRingEnd ℂ t).re := by rwa [conj_re]
  have ht0 : t ≠ 0 := fun h ↦ by norm_num [h] at ht
  have htc0 : starRingEnd ℂ t ≠ 0 := by simpa using ht0
  have hΓc : Gammaℝ (starRingEnd ℂ t) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓt : Gammaℝ t ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have e (X : ℂ) : completedRiemannZeta₀ X = completedRiemannZeta X + 1 / X + 1 / (1 - X) := by
    linear_combination -completedRiemannZeta_eq X
  simp only [e, completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ htc0 hΓc,
    completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ ht0 hΓt, map_add, map_mul, map_div₀, map_one,
    map_sub, riemannZeta_conj, Gammaℝ_conj, conj_conj]

/-- Conjugation symmetry of the entire completed zeta `Λ₀`: `Λ₀(conj s) = conj (Λ₀ s)`. -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  rw [← conj_completedRiemannZeta₀_conj s, conj_conj]

/-- **The Riemann ξ function** `ξ(s) = ½ s (s - 1) Λ(s)`, in the manifestly entire form
`ξ(s) = ½ s (s - 1) Λ₀(s) + ½`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1)) * completedRiemannZeta₀ s + 1 / 2

/-- Away from the poles `s = 0, 1` of `Λ`, the ξ function is `½ s (s - 1) Λ(s)`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s := by
  have h₁ : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs₁)
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring

/-- The Riemann ξ function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi :=
  (((differentiable_id.mul (differentiable_id.sub_const 1)).const_mul (1 / 2)).mul
    differentiable_completedZeta₀).add_const (1 / 2)

/-- The Riemann ξ function is analytic on a neighbourhood of every point. -/
theorem analyticOnNhd_riemannXi : AnalyticOnNhd ℂ riemannXi Set.univ :=
  differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ

/-- The functional equation for ξ: `ξ(1 - s) = ξ(s)`. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring

/-- The value of ξ at the pole `s = 0` of `Λ`. -/
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

/-- The value of ξ at the pole `s = 1` of `Λ`. -/
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

/-- Conjugation symmetry of the Riemann ξ function: `ξ(conj s) = conj (ξ s)`. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  simp [riemannXi, completedRiemannZeta₀_conj, map_ofNat]

/-- Away from the poles `s = 0, 1` of `Λ`, with `Γ_ℝ(s) ≠ 0`, ξ factors as the prefactor
`½ s (s - 1) Γ_ℝ(s)` times ζ. -/
theorem riemannXi_eq_prefactor_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * Gammaℝ s * riemannZeta s := by
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ hs0 hΓ]
  ring

/-- Points of the critical strip `0 < Re s < 1` avoid the poles `0` and `1` of `Λ`. -/
private theorem ne_zero_and_ne_one {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : s ≠ 0 ∧ s ≠ 1 :=
  ⟨fun h ↦ by simp [h] at h0, fun h ↦ by simp [h] at h1⟩

/-- On the critical strip `0 < Re s < 1`, ξ factors as the analytic non-vanishing prefactor
`½ s (s - 1) Γ_ℝ(s)` times ζ. -/
private theorem riemannXi_eq_prefactor_mul_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * Gammaℝ s * riemannZeta s :=
  riemannXi_eq_prefactor_mul (ne_zero_and_ne_one h0 h1).1 (ne_zero_and_ne_one h0 h1).2
    (Gammaℝ_ne_zero_of_re_pos h0)

/-- **The non-vanishing of the ξ prefactor `½ s (s - 1) Γ_ℝ(s)`**, under exactly the hypotheses
of the factorisation `riemannXi_eq_prefactor_mul`. -/
theorem prefactor_ne_zero_of {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    (1 / 2 : ℂ) * (s * (s - 1)) * Gammaℝ s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))) hΓ

/-- The non-vanishing of the strip prefactor `½ s (s - 1) Γ_ℝ(s)`. -/
private theorem prefactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (1 / 2 : ℂ) * (s * (s - 1)) * Gammaℝ s ≠ 0 :=
  prefactor_ne_zero_of (ne_zero_and_ne_one h0 h1).1 (ne_zero_and_ne_one h0 h1).2
    (Gammaℝ_ne_zero_of_re_pos h0)

/-- **Zeros of ξ on the critical strip are exactly the zeros of ζ.** -/
theorem riemannXi_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [riemannXi_eq_prefactor_mul_riemannZeta h0 h1, mul_eq_zero,
    or_iff_right (prefactor_ne_zero h0 h1)]

/-- **The order of ξ agrees with the order of ζ on the critical strip.** -/
theorem meromorphicOrderAt_riemannXi_eq_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    meromorphicOrderAt riemannXi s = meromorphicOrderAt riemannZeta s := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (Complex.isOpen_re_gt 0).inter (isOpen_lt continuous_re continuous_const)
  have heq : riemannXi =ᶠ[nhds s]
      (fun z : ℂ ↦ (1 / 2) * (z * (z - 1)) * Gammaℝ z) * riemannZeta := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with z hz
    simpa only [Pi.mul_apply] using riemannXi_eq_prefactor_mul_riemannZeta hz.1 hz.2
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_mul_of_ne_zero
    ((by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ (1 / 2 : ℂ) * (z * (z - 1))) s).mul
      (analyticAt_Gammaℝ h0)) (prefactor_ne_zero h0 h1)
