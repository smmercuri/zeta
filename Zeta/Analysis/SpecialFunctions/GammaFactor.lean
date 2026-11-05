/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# The functional-equation factor of the Riemann zeta function

The factor `χ` characterised by `ζ(s) = χ(s) ζ(1-s)` is the shape in which Siegel states the
identity behind the Riemann–Siegel formula (`riemann_siegel_zero.tex`, `def:rsz_mirror`). It must
be *defined* by a `Γ`-quotient — here `Γ_ℝ(1-s)/Γ_ℝ(s)` in Deligne's archimedean factor of
`Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean`, equivalently `π^{s-1/2} Γ((1-s)/2) / Γ(s/2)`
— and never by the classical product `2^s π^{s-1} sin(πs/2) Γ(1-s)`: `Complex.Gamma` takes the junk
value `0` at its poles, so the product form collapses to `0` at every even integer `s ≥ 2`, where
the true value is not `0` — for instance `χ(2) = -2π²`. The quotient form inverts `Γ` rather than
multiplying it, so its only junk values are at the poles `s = 1, 3, 5, …` of `Γ((1-s)/2)`, and at
`s = 0, -2, -4, …` the junk value `1/Γ(0) = 0` of the denominator agrees with the true `χ(s) = 0`.

Both classical identities therefore carry an exclusion, and the two excluded sets differ: at
`s = 1, 3, 5, …` the two sides of the cosine identity disagree, and at `s = 2, 4, 6, …` the two
sides of the product identity do.

## Main results

* `Complex.chi`: the factor itself;
* `Complex.chi_eq_cpow_mul_Gamma_div_Gamma`: `χ(s) = π^{s-1/2} Γ((1-s)/2) / Γ(s/2)`;
* `Complex.inv_Gammaℂ`: `Γ_ℂ(s)⁻¹ = (2π)^s / (2Γ(s))`;
* `Complex.chi_mul_cos`: `χ(s) cos(πs/2) = (2π)^s / (2Γ(s))`, off `{1, 3, 5, …}`;
* `Complex.chi_eq_two_cpow_mul_cpow_mul_sin_mul_Gamma`:
  `χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s)`, off `{2, 4, 6, …}`;
* `Complex.Gammaℝ_conj`: `Γ_ℝ(s̄) = conj (Γ_ℝ(s))`;
* `Complex.differentiableAt_chi`: `χ` is holomorphic off `{1, 3, 5, …}`.
-/
@[expose] public section


open scoped Real

namespace Complex

/-- The **functional-equation factor** `χ(s) = Γ_ℝ(1-s) / Γ_ℝ(s)` of the Riemann zeta function,
the factor for which `ζ(s) = χ(s) ζ(1-s)`. -/
noncomputable def chi (s : ℂ) : ℂ :=
  Gammaℝ (1 - s) / Gammaℝ s

/-- **The `Γ`-quotient form of `χ`**, `χ(s) = π^{s-1/2} Γ((1-s)/2) / Γ(s/2)`. -/
theorem chi_eq_cpow_mul_Gamma_div_Gamma (s : ℂ) :
    chi s = (π : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) / Gamma (s / 2) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [chi, Gammaℝ_def, Gammaℝ_def, ← div_mul_div_comm, ← cpow_sub _ _ hπ,
    show -(1 - s) / 2 - -s / 2 = s - 1 / 2 by ring, mul_div_assoc]

/-- **The reciprocal of Deligne's complex archimedean factor**,
`Γ_ℂ(s)⁻¹ = (2π)^s / (2 Γ(s))`. -/
theorem inv_Gammaℂ (s : ℂ) : (Gammaℂ s)⁻¹ = (2 * π) ^ s / (2 * Gamma s) := by
  rw [Gammaℂ_def, cpow_neg, mul_inv, mul_inv, inv_inv, div_eq_mul_inv, mul_inv]
  ring

/-- **The identity `χ(s) cos(πs/2) = (2π)^s / (2 Γ(s))`**, off `s = 1, 3, 5, …`. -/
theorem chi_mul_cos {s : ℂ} (hs : ∀ n : ℕ, s ≠ 2 * n + 1) :
    chi s * cos ((π : ℂ) * s / 2) = (2 * π) ^ s / (2 * Gamma s) := by
  rw [chi, ← inv_Gammaℂ]
  by_cases hcos : cos ((π : ℂ) * s / 2) = 0
  · -- `s` is an odd integer; it cannot be positive, so `Γ(s) = 0` and both sides vanish
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.1 hcos
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have hsk : s = 2 * (k : ℂ) + 1 :=
      mul_left_cancel₀ hπ (by linear_combination 2 * hk : (π : ℂ) * s = (π : ℂ) * (2 * k + 1))
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0 with n
      exact absurd hsk (hs n)
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m + 1) := ⟨(-k - 1).toNat, by omega⟩
      have hGamma : Gamma s = 0 := by
        refine (Gamma_eq_zero_iff s).2 ⟨2 * m + 1, ?_⟩
        rw [hsk]
        push_cast
        ring
      rw [hcos, mul_zero, Gammaℂ_def, hGamma, mul_zero, inv_zero]
  · -- off the odd integers the reflection formula may be inverted
    have hodd : ∀ n : ℕ, s ≠ -(2 * n + 1) := by
      intro n hsn
      refine hcos ?_
      rw [cos_eq_zero_iff]
      exact ⟨-(n + 1), by rw [hsn]; push_cast; ring⟩
    have hinv : Gammaℝ (1 - s) / Gammaℝ s = (Gammaℂ s * cos ((π : ℂ) * s / 2))⁻¹ := by
      rw [← Gammaℝ_div_Gammaℝ_one_sub hodd, inv_div]
    rw [hinv, mul_inv, inv_mul_cancel_right₀ hcos]

/-- **The classical product formula `χ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s)`**, off `s = 2, 4, 6, …`.
-/
theorem chi_eq_two_cpow_mul_cpow_mul_sin_mul_Gamma {s : ℂ} (hs : ∀ n : ℕ, s ≠ 2 * (n + 1)) :
    chi s = 2 ^ s * (π : ℂ) ^ (s - 1) * sin ((π : ℂ) * s / 2) * Gamma (1 - s) := by
  have hodd : ∀ n : ℕ, (1 : ℂ) - s ≠ -(2 * n + 1) := fun n h ↦ hs n (by linear_combination -h)
  have key := Gammaℝ_div_Gammaℝ_one_sub hodd
  rw [show (1 : ℂ) - (1 - s) = s by ring] at key
  have h2 : (2 : ℂ) ^ (s - 1) * 2 = 2 ^ s := by
    nth_rewrite 2 [show (2 : ℂ) = 2 ^ (1 : ℂ) by rw [cpow_one]]
    rw [← cpow_add _ _ two_ne_zero]
    congr 1
    ring
  rw [chi, key, Gammaℂ_def, show (π : ℂ) * (1 - s) / 2 = π / 2 - π * s / 2 by ring,
    cos_pi_div_two_sub, show -(1 - s) = s - 1 by ring,
    show ((2 : ℂ) * π) = ((2 : ℝ) : ℂ) * ((π : ℝ) : ℂ) by norm_num,
    mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
  push_cast
  rw [← h2]
  ring

/-- **Deligne's real archimedean factor commutes with conjugation**, `Γ_ℝ(s̄) = conj (Γ_ℝ(s))`. -/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Gammaℝ s) := by
  have harg : ((π : ℝ) : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact fun h ↦ Real.pi_ne_zero h.symm
  have hpow : ((π : ℝ) : ℂ) ^ (-(starRingEnd ℂ s) / 2)
      = starRingEnd ℂ (((π : ℝ) : ℂ) ^ (-s / 2)) := by
    have h := conj_cpow ((π : ℝ) : ℂ) (-(starRingEnd ℂ s) / 2) harg
    rw [conj_ofReal] at h
    rw [h]
    congr 2
    simp only [map_div₀, map_neg, conj_conj, map_ofNat]
  have hGam : Gamma (starRingEnd ℂ s / 2) = starRingEnd ℂ (Gamma (s / 2)) := by
    rw [← Gamma_conj]
    congr 1
    simp only [map_div₀, map_ofNat]
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, hpow, hGam]

/-- **`χ` is holomorphic off `s = 1, 3, 5, …`.** -/
theorem differentiableAt_chi {s : ℂ} (hs : ∀ n : ℕ, s ≠ 2 * n + 1) : DifferentiableAt ℂ chi s := by
  have hfun : chi = fun z : ℂ ↦ (π : ℂ) ^ (z - 1 / 2) * Gamma ((1 - z) / 2) * (Gamma (z / 2))⁻¹ :=
    funext fun z ↦ by rw [chi_eq_cpow_mul_Gamma_div_Gamma, div_eq_mul_inv]
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ (π : ℂ) ^ (z - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.2 Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ Gamma ((1 - z) / 2)) s :=
    (differentiableAt_Gamma _ fun m hm ↦ hs m (by linear_combination -2 * hm)).comp s
      (((differentiableAt_const 1).sub differentiableAt_id).div_const 2)
  have h3 : DifferentiableAt ℂ (fun z : ℂ ↦ (Gamma (z / 2))⁻¹) s :=
    (differentiable_one_div_Gamma _).comp s (differentiableAt_id.div_const 2)
  rw [hfun]
  exact (h1.mul h2).mul h3

end Complex
