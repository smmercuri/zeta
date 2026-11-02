/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.Hadamard
public import Zeta.Hadamard.ZeroSummability
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The canonical product of `ξ` and its entire zero-free quotient

The canonical product `riemannXiCanonicalProduct` instantiated at the concrete multiplicity
enumeration `riemannXiZeros` of the zeros of `ξ`, and the entire zero-free quotient `g = ξ/P`
(`hadamard_factorization.tex`).

## Main results

* `riemannXiZeros` (`def:hf_prod`): the multiplicity enumeration `ρ` of the zeros of `ξ`.
* `divisor_riemannXiCanonicalProduct_riemannXiZeros_eq`: the divisor of `P` equals that of `ξ`.
* `differentiable_riemannXi_div_canonicalProduct` (`lem:hf_quot`): an entire, nowhere-vanishing
  `g` with `ξ = g · P` and `g(0) = 1/2`.
* `exists_entire_log_riemannXi_div_canonicalProduct` (`lem:hf_eq_exp`): `ξ = exp(h) · P` with `h`
  entire.
-/
@[expose] public section


open Complex Filter Topology MeromorphicOn Set Function Metric


/-- The index type enumerating the zeros of `ξ` with multiplicity: a zero `z` of `ξ`
(i.e. `z ∈ support D`, where `D = divisor ξ`) is repeated `D z` times. -/
abbrev RiemannXiZerosIndex : Type :=
  (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
    Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat

/-- The enumeration `ρ` of the zeros of `ξ` with multiplicity (`def:hf_prod`). -/
abbrev riemannXiZeros (i : RiemannXiZerosIndex) : ℂ := (i.1 : ℂ)

/-- No enumerated zero is `0`. -/
theorem riemannXiZeros_ne_zero (i : RiemannXiZerosIndex) : riemannXiZeros i ≠ 0 := by
  intro h
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (i.1 : ℂ) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [show (i.1 : ℂ) = 0 from h, divisor_riemannXi_apply_zero] at hmem
  exact hmem rfl

private theorem untop₀_map_natCast (x : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) x).untop₀ = (x.toNat : ℤ) := by
  induction x using ENat.recTopCoe <;> simp

/-- For an entire `f`, the value of its divisor at `z` is the analytic order (as an integer). -/
theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ⊤) (z : ℂ) :
    MeromorphicOn.divisor f ⊤ z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ _),
    (hf z (Set.mem_univ _)).meromorphicOrderAt_eq, untop₀_map_natCast]
  rfl

/-- The fibre of the enumeration over a point `z` has exactly `(divisor ξ z)` elements. -/
theorem ncard_setOf_riemannXiZeros_eq (z : ℂ) :
    {i | riemannXiZeros i = z}.ncard = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i
      simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset]
    calc {i : RiemannXiZerosIndex |
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)}.ncard
        = Nat.card {i : RiemannXiZerosIndex //
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)} :=
          (Nat.card_coe_set_eq _).symm
      _ = Nat.card (Fin (MeromorphicOn.divisor riemannXi ⊤ z).toNat) :=
          Nat.card_congr (Equiv.sigmaSubtype
            (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support))
      _ = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by simp
  · have hempty : {i | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h
      exact hz (h ▸ i.1.2)
    simp only [Function.mem_support, ne_eq, not_not] at hz
    rw [hempty, Set.ncard_empty, hz, Int.toNat_zero]

/-- **Divisor matching (`lem:hf_quot`).** The divisor of the canonical product `P` over the
enumeration `riemannXiZeros` coincides with the divisor of `ξ`. -/
theorem divisor_riemannXiCanonicalProduct_riemannXiZeros_eq :
    MeromorphicOn.divisor (riemannXiCanonicalProduct riemannXiZeros) ⊤
      = MeromorphicOn.divisor riemannXi ⊤ := by
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPanalytic : AnalyticOnNhd ℂ (riemannXiCanonicalProduct riemannXiZeros) ⊤ :=
    (differentiable_riemannXiCanonicalProduct riemannXiZeros hsum).differentiableOn.analyticOnNhd
      isOpen_univ
  ext z
  have hξnn : 0 ≤ MeromorphicOn.divisor riemannXi ⊤ z := by
    rw [divisor_eq_analyticOrderNatAt analyticOnNhd_riemannXi z]; positivity
  rw [divisor_eq_analyticOrderNatAt hPanalytic z,
    analyticOrderNatAt_riemannXiCanonicalProduct riemannXiZeros hsum riemannXiZeros_ne_zero z,
    ncard_setOf_riemannXiZeros_eq z, Int.toNat_of_nonneg hξnn]

/-- **The quotient `g = ξ/P` is entire and zero-free (`lem:hf_quot`).** There is an entire function
`g` with `g(s) ≠ 0` for all `s`, `ξ(s) = g(s) · P(s)`, and `g(0) = 1/2`. -/
theorem differentiable_riemannXi_div_canonicalProduct :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ s, g s ≠ 0) ∧
      (∀ s, riemannXi s = g s * riemannXiCanonicalProduct riemannXiZeros s) ∧ g 0 = 1 / 2 := by
  set P := riemannXiCanonicalProduct riemannXiZeros with hP
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPdiff : Differentiable ℂ P := differentiable_riemannXiCanonicalProduct riemannXiZeros hsum
  have hPanalytic : AnalyticOnNhd ℂ P ⊤ := hPdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hξanalytic : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hPmero : MeromorphicOn P ⊤ := hPanalytic.meromorphicOn
  have hξmero : MeromorphicOn riemannXi ⊤ := hξanalytic.meromorphicOn
  have hP0 : P 0 = 1 := riemannXiCanonicalProduct_zero riemannXiZeros
  have hP0ne : P 0 ≠ 0 := by rw [hP0]; norm_num
  -- The meromorphic quotient `F = ξ/P`.
  set F : ℂ → ℂ := fun s ↦ riemannXi s / P s with hF
  have hFmero : MeromorphicOn F ⊤ := hξmero.div hPmero
  -- Orders are everywhere finite (an entire function non-vanishing somewhere on connected `ℂ`).
  have hmordne : ∀ (f : ℂ → ℂ) (x : ℂ), AnalyticOnNhd ℂ f ⊤ → f x ≠ 0 →
      ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := fun f x hf hx z hz ↦
    meromorphicOrderAt_ne_top_of_isPreconnected hf.meromorphicOn isPreconnected_univ
      (Set.mem_univ x) hz (by
        rw [(hf x (Set.mem_univ _)).meromorphicOrderAt_eq,
          (hf x (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hx]; simp)
  have hξne := hmordne riemannXi 0 hξanalytic (by rw [riemannXi_zero]; norm_num)
  have hPne := hmordne P 0 hPanalytic hP0ne
  have hPinvne : ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt P⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    simpa using hPne z hz
  -- `divisor F = divisor ξ - divisor P = 0`.
  have hdivF : MeromorphicOn.divisor F ⊤ = 0 := by
    have hFeq : F = riemannXi * P⁻¹ := by
      funext s; simp only [hF, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hFeq, MeromorphicOn.divisor_mul hξmero hPmero.inv hξne hPinvne,
      MeromorphicOn.divisor_inv, hP, divisor_riemannXiCanonicalProduct_riemannXiZeros_eq,
      add_neg_cancel]
  -- The entire, zero-free representative `g`.
  set g := toMeromorphicNFOn F ⊤ with hg
  have hgNF : MeromorphicNFOn g ⊤ := meromorphicNFOn_toMeromorphicNFOn F ⊤
  have hdivg0 : MeromorphicOn.divisor g ⊤ = 0 :=
    (MeromorphicOn.divisor_of_toMeromorphicNFOn hFmero).trans hdivF
  have hganalytic : AnalyticOnNhd ℂ g ⊤ :=
    hgNF.divisor_nonneg_iff_analyticOnNhd.mp (le_of_eq hdivg0.symm)
  have hgdiff : Differentiable ℂ g := fun s ↦ (hganalytic s (Set.mem_univ _)).differentiableAt
  -- `g(0) = ξ(0)/P(0) = 1/2`.
  have hFanalytic0 : AnalyticAt ℂ F 0 := by
    rw [hF]; exact (hξanalytic 0 (Set.mem_univ _)).div (hPanalytic 0 (Set.mem_univ _)) hP0ne
  have hF0 : F 0 = 1 / 2 := by
    rw [hF]; change riemannXi 0 / P 0 = 1 / 2; rw [riemannXi_zero, hP0]; norm_num
  have hg0 : g 0 = 1 / 2 := by
    have h1 := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hFmero (Set.mem_univ (0 : ℂ))
    rw [toMeromorphicNFAt_eq_self.mpr hFanalytic0.meromorphicNFAt] at h1
    rw [hg, h1.eq_of_nhds, hF0]
  -- `g` is nowhere zero (divisor `0` and not identically zero).
  have hgne : ∀ s, g s ≠ 0 := fun s ↦ by
    rw [← (hgNF (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff]
    have hne : meromorphicOrderAt g s ≠ ⊤ :=
      hmordne g 0 hganalytic (by rw [hg0]; norm_num) s (Set.mem_univ _)
    have hdiv : (meromorphicOrderAt g s).untop₀ = 0 := by
      rw [← MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ s), hdivg0]; rfl
    exact (WithTop.untop₀_eq_zero.mp hdiv).resolve_right hne
  -- `ξ = g · P` everywhere, by the codiscrete identity theorem.
  have hFg : F =ᶠ[codiscreteWithin ⊤] g := toMeromorphicNFOn_eqOn_codiscrete hFmero
  have hPneSet : P ⁻¹' {0}ᶜ ∈ codiscreteWithin (⊤ : Set ℂ) :=
    hPanalytic.preimage_zero_mem_codiscreteWithin hP0ne (Set.mem_univ _) isConnected_univ
  have hgPeqξ : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
    have e1 : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] (fun s ↦ F s * P s) :=
      hFg.symm.mul (EventuallyEq.refl _ P)
    have e2 : (fun s ↦ F s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
      filter_upwards [hPneSet] with s hs
      have hsne : P s ≠ 0 := by
        simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      simp only [hF]
      exact div_mul_cancel₀ (riemannXi s) hsne
    exact e1.trans e2
  have hgPanalytic : AnalyticOnNhd ℂ (fun s ↦ g s * P s) ⊤ :=
    fun z hz ↦ (hganalytic z hz).mul (hPanalytic z hz)
  -- `𝓝[≠] 0` refines the codiscrete filter, so the codiscrete equality is frequent near `0`.
  have hle : 𝓝[≠] (0 : ℂ) ≤ codiscreteWithin (⊤ : Set ℂ) := by
    rw [Filter.codiscreteWithin]
    refine le_iSup₂_of_le (0 : ℂ) (Set.mem_univ _) (le_of_eq ?_)
    rw [Set.top_eq_univ, ← Set.compl_eq_univ_sdiff]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun s ↦ g s * P s) z = riemannXi z :=
    (hgPeqξ.filter_mono hle).frequently
  exact ⟨g, hgdiff, hgne, fun s ↦ (hgPanalytic.eqOn_of_preconnected_of_frequently_eq hξanalytic
    isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ s)).symm, hg0⟩

/-- **Global holomorphic logarithm of the quotient (`lem:hf_eq_exp`).** There is an entire `h`
with `h(0) = log(1/2)` and `ξ(s) = exp(h(s)) · P(s)` for all `s`. -/
theorem exists_entire_log_riemannXi_div_canonicalProduct :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (1 / 2) ∧
      (∀ s, riemannXi s = Complex.exp (h s) *
        riemannXiCanonicalProduct riemannXiZeros s) := by
  obtain ⟨g, hgdiff, hgne, hgP, hg0⟩ := differentiable_riemannXi_div_canonicalProduct
  -- The logarithmic derivative `φ = g'/g` is entire (`deriv g` is analytic, `g` is nowhere zero).
  set φ : ℂ → ℂ := fun s ↦ deriv g s / g s with hφ
  have hgana : AnalyticOnNhd ℂ g Set.univ := hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hderivdiff : Differentiable ℂ (deriv g) :=
    fun x ↦ (hgana.deriv x (Set.mem_univ _)).differentiableAt
  have hφdiff : Differentiable ℂ φ := hderivdiff.div hgdiff hgne
  -- A global primitive `H` of `φ` on the simply connected `ℂ`, normalised at `H(0) = 0`.
  obtain ⟨H, hH0, hHderiv⟩ := hφdiff.isExactOn_univ.with_val_at 0 0
  have hHderiv' : ∀ x, HasDerivAt H (φ x) x := fun x ↦ hHderiv x (Set.mem_univ _)
  have hHdiff : Differentiable ℂ H := fun x ↦ (hHderiv' x).differentiableAt
  -- `k := g · exp(-H)` has zero derivative, hence is the constant `k(0) = 1/2`.
  set k : ℂ → ℂ := fun s ↦ g s * Complex.exp (-H s) with hk
  have hkderiv : ∀ x, HasDerivAt k 0 x := by
    intro x
    have hg_deriv : HasDerivAt g (deriv g x) x := (hgdiff x).hasDerivAt
    have hexp_deriv := ((hHderiv' x).neg).cexp
    -- The product derivative `g'·e^{-H} - g·(g'/g)·e^{-H}` cancels to `0`.
    have hval : deriv g x * Complex.exp ((-H) x) +
        g x * (Complex.exp ((-H) x) * -φ x) = 0 := by
      simp only [hφ]
      field_simp [hgne x]
      ring
    exact hval ▸ hg_deriv.mul hexp_deriv
  have hkdiff : Differentiable ℂ k := fun x ↦ (hkderiv x).differentiableAt
  have hkconst : ∀ s, k s = k 0 :=
    fun s ↦ is_const_of_deriv_eq_zero hkdiff (fun x ↦ (hkderiv x).deriv) s 0
  have hk0 : k 0 = 1 / 2 := by
    simp only [hk, hH0, neg_zero, Complex.exp_zero, mul_one, hg0]
  -- Hence `g s = exp(H s + log(1/2))`, and `ξ = exp(h)·P` with `h := H + log(1/2)`.
  refine ⟨fun s ↦ H s + Complex.log (1 / 2), hHdiff.add_const _, by simp [hH0], fun s ↦ ?_⟩
  have hk_eval : g s * Complex.exp (-H s) = 1 / 2 := by
    have := hkconst s; rw [hk0] at this; simpa only [hk] using this
  have hexp : Complex.exp (H s + Complex.log (1 / 2)) = g s := by
    rw [Complex.exp_add, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0), ← hk_eval,
      Complex.exp_neg, mul_comm (g s), ← mul_assoc,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]
  rw [hgP s, hexp]

