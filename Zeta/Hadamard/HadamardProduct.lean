/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardLinear
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The Hadamard factorisation of `ξ`

Identification of the constants in `ξ = exp(A + B·s) · P` and assembly of the genus-`1` Hadamard
product (`hadamard_factorization.tex`).

## Main results

* `logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero`: `P'/P (0) = 0`.
* `log_riemannXi_div_canonicalProduct_const_eq` (`lem:hf_constants`): `exp A = 1/2`,
  `B = ξ'/ξ(0)`, and `B` is real.
* `riemannXi_eq_hadamard_product` (`thm:hf_hadamard`): there is a real `B` with
  `ξ(s) = ½ · exp(B·s) · ∏ᵢ (1 - s/ρᵢ) exp(s/ρᵢ)` for all `s`.
-/
@[expose] public section


open Complex Filter Topology Set
open scoped ComplexConjugate


/-- **The logarithmic derivative of the canonical product vanishes at `0`:** `P'/P (0) = 0`. -/
theorem logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) 0 = 0 := by
  set ρ := riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i) with hf
  -- Each factor is differentiable on `ℂ` and equals `1` at `0`.
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hf0 : ∀ i, f i 0 = 1 := fun i ↦ by simp [hf]
  -- Each factor logarithmic derivative vanishes at `0` (because `E₁'(0) = 0`).
  have hlog0 : ∀ i, logDeriv (f i) 0 = 0 := fun i ↦ by
    have hu : HasDerivAt (fun s : ℂ ↦ s / ρ i) (ρ i)⁻¹ 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℂ)).div_const (ρ i)
    have hde : HasDerivAt (f i) 0 0 := by
      simpa [hf, Function.comp_def] using (hasDerivAt_weierstrassE1 ((0 : ℂ) / ρ i)).comp 0 hu
    rw [logDeriv_apply, hde.deriv, hf0 i, zero_div]
  -- `logDeriv P(0) = ∑ᵢ logDeriv (f i)(0) = 0`.
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ (0 : ℂ))
    (fun i ↦ by rw [hf0 i]; norm_num) hd (by simp only [hlog0]; exact summable_zero)
    ((hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ
      summable_inv_norm_sq_riemannXiZeros).multipliableLocallyUniformlyOn)
    (by simp only [hf0, tprod_one]; norm_num)
  simp only [hlog0, tsum_zero] at hkey
  -- `(∏' i, f i ·)` is `riemannXiCanonicalProduct ρ` by definition.
  exact hkey

/-- **The logarithmic derivative of `ξ` at `0` reads off the exponent.** If `ξ = exp(h)·P` with `h`
entire, then `logDeriv ξ (0) = h'(0)`. -/
theorem logDeriv_riemannXi_zero_eq_deriv {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = deriv h 0 := by
  have hP0ne : riemannXiCanonicalProduct riemannXiZeros 0 ≠ 0 := by
    rw [riemannXiCanonicalProduct_zero]; norm_num
  rw [funext hrep, logDeriv_mul (f := fun s ↦ Complex.exp (h s))
      (g := riemannXiCanonicalProduct riemannXiZeros) 0 (Complex.exp_ne_zero _) hP0ne
      (hdiff 0).hasDerivAt.cexp.differentiableAt
      (differentiable_riemannXiCanonicalProduct riemannXiZeros
        summable_inv_norm_sq_riemannXiZeros 0),
    show (fun s ↦ Complex.exp (h s)) = Complex.exp ∘ h from rfl,
    logDeriv_comp (Complex.differentiable_exp (h 0)) (hdiff 0), Complex.logDeriv_exp,
    logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero]
  simp

/-- **Identification of the constants (`lem:hf_constants`).** Writing `ξ = exp(h)·P` with the
exponent affine, `h(s) = A + B·s`, one has `exp A = 1/2`, `B = ξ'/ξ(0)`, and `B` is real. -/
theorem log_riemannXi_div_canonicalProduct_const_eq {h : ℂ → ℂ} {A B : ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s)
    (haffine : ∀ s, h s = A + B * s) :
    Complex.exp A = 1 / 2 ∧ B = logDeriv riemannXi 0 ∧ conj B = B := by
  -- `exp A = 1/2`, by evaluating `ξ = exp(h)·P` at `0` (`h 0 = A`, `P 0 = 1`, `ξ 0 = 1/2`).
  have hexpA : Complex.exp A = 1 / 2 := by
    have h0 := hrep 0
    rw [riemannXi_zero, riemannXiCanonicalProduct_zero, mul_one, haffine 0, mul_zero,
      add_zero] at h0
    exact h0.symm
  -- `B = ξ'/ξ(0) = h'(0)`, by `logDeriv_riemannXi_zero_eq_deriv`.
  have hBeq : B = logDeriv riemannXi 0 := by
    rw [logDeriv_riemannXi_zero_eq_deriv hdiff hrep, funext haffine]; simp
  -- Reality of `ξ'(0)`: `conj ∘ ξ ∘ conj = ξ`, so `deriv ξ = conj ∘ deriv ξ ∘ conj`, and at `0`
  -- (a conjugation-fixed point) this reads `ξ'(0) = conj (ξ'(0))`.
  have hsym : conj ∘ riemannXi ∘ conj = riemannXi := by
    funext s; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have hreal : conj (deriv riemannXi 0) = deriv riemannXi 0 := by
    simpa using congrFun (by rw [← deriv_conj_conj, hsym] :
      conj ∘ deriv riemannXi ∘ conj = deriv riemannXi) 0
  refine ⟨hexpA, hBeq, ?_⟩
  rw [hBeq, logDeriv_apply, map_div₀, hreal, riemannXi_zero, map_div₀, map_one, map_ofNat]

/-- **Hadamard factorisation of `ξ` (`thm:hf_hadamard`, `lem:lb_pf_hadamard`).** There is a real
constant `B = ξ'/ξ(0)` with `ξ(s) = ½ · exp(B·s) · ∏ᵢ (1 - s/ρᵢ) exp(s/ρᵢ)` for all `s`, the
product running over the multiplicity enumeration `riemannXiZeros` of the nontrivial zeros. -/
theorem riemannXi_eq_hadamard_product :
    ∃ B : ℝ, ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s := by
  obtain ⟨h, hdiff, _, hrep⟩ := exists_entire_log_riemannXi_div_canonicalProduct
  obtain ⟨A, B, haffine⟩ := exists_affine_log_riemannXi_div_canonicalProduct hdiff hrep
  obtain ⟨hexpA, _, hBreal⟩ := log_riemannXi_div_canonicalProduct_const_eq hdiff hrep haffine
  refine ⟨B.re, fun s ↦ ?_⟩
  have hBre : (B.re : ℂ) = B := Complex.conj_eq_iff_re.mp hBreal
  rw [hrep s, haffine s, Complex.exp_add, hexpA, hBre]

