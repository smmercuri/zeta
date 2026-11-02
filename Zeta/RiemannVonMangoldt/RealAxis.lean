/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.EulerMaclaurin.Continuation
public import Zeta.RiemannXi
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Non-vanishing of `ξ` on the real segment `[-1, 2]`

The bottom edge of the counting rectangle `[-1, 2] × [0, T]` of the Riemann–von Mangoldt formula
is the real segment `[-1, 2]`, on which `ξ` does not vanish.

## Main results

- `riemannZeta_ofReal_neg_of_mem_Ioo`: for real `σ ∈ (0, 1)`, `ζ(σ)` is real and negative.
- `riemannXi_ofReal_ne_zero_of_mem_Icc`: for real `σ ∈ [-1, 2]`, `ξ(σ) ≠ 0`.
-/
@[expose] public section


open Complex Set

/-- **`ζ` is real and negative on the open real segment `(0, 1)`.** -/
theorem riemannZeta_ofReal_neg_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (riemannZeta (σ : ℂ)).im = 0 ∧ (riemannZeta (σ : ℂ)).re < 0 :=
  ⟨Complex.conj_eq_iff_im.mp (by simpa using (riemannZeta_conj (σ : ℂ)).symm),
    riemannZeta_ofReal_re_neg_of_mem_Ioo hσ⟩

/-- For real `σ > 1` the value `ξ(σ)` is nonzero. -/
private theorem riemannXi_ofReal_ne_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    riemannXi (σ : ℂ) ≠ 0 := by
  have hσ0 : (σ : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; linarith
  have hσ1 : (σ : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  have hΓ : Gammaℝ (σ : ℂ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; linarith)
  rw [riemannXi_eq_prefactor_mul hσ0 hσ1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hσ0 hσ1 hΓ)
    (riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith))

/-- **`ξ` has no zeros on the real segment `[-1, 2]`.** -/
theorem riemannXi_ofReal_ne_zero_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    riemannXi (σ : ℂ) ≠ 0 := by
  obtain ⟨hlo, hhi⟩ := hσ
  rcases lt_trichotomy σ 0 with hneg | rfl | hpos
  · -- `σ ∈ [-1, 0)`: reflect via `ξ(s) = ξ(1 - s)` to `1 - σ ∈ (1, 2]`.
    rw [show ((σ : ℂ)) = 1 - ((1 - σ : ℝ) : ℂ) from by push_cast; ring, riemannXi_one_sub]
    exact riemannXi_ofReal_ne_zero_of_one_lt (by linarith)
  · rw [Complex.ofReal_zero, riemannXi_zero]; norm_num
  · rcases lt_trichotomy σ 1 with h1 | rfl | h1
    · -- `σ ∈ (0, 1)`: `ξ(σ) = 0 ↔ ζ(σ) = 0`, and `ζ(σ) < 0`.
      exact fun h ↦ (riemannZeta_ofReal_neg_of_mem_Ioo ⟨hpos, h1⟩).2.ne
        (by rw [(riemannXi_eq_zero_iff (by simpa using hpos) (by simpa using h1)).mp h,
          Complex.zero_re])
    · rw [Complex.ofReal_one, riemannXi_one]; norm_num
    · exact riemannXi_ofReal_ne_zero_of_one_lt h1
