/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardProduct

/-!
# Partial-fraction expansion of `ξ'/ξ` and `ζ'/ζ`

The partial-fraction expansion of `ξ'/ξ` over the nontrivial zeros `ρᵢ`, and the Davenport
explicit formula for `ζ'/ζ` that follows from it (`sec:lb_pf`).

## Main results

* `logDeriv_riemannXi_eq` (`lem:lb_pf_xi`): for `s` not a nontrivial zero,
  `ξ'/ξ(s) = ξ'/ξ(0) + ∑ᵢ (1/(s - ρᵢ) + 1/ρᵢ)`.
* `logDeriv_riemannZeta_eq` (`lem:lb_pf_zeta`): for `0 < Re s`, `s ≠ 1` not a nontrivial zero,
  `ζ'/ζ(s) = ξ'/ξ(0) - 1/s - 1/(s-1) + ½ log π - ½ ψ(s/2) + ∑ᵢ (1/(s - ρᵢ) + 1/ρᵢ)`.
-/
@[expose] public section


open Complex Filter Topology Set
open scoped Real


/-- The logarithmic derivative of an elementary factor `s ↦ E₁(s/ρ) = (1 - s/ρ) exp(s/ρ)` away
from its zero. -/
private lemma logDeriv_weierstrassE1_div {ρ : ℂ} (hρ : ρ ≠ 0) {s : ℂ} (hs : s ≠ ρ) :
    logDeriv (fun z ↦ weierstrassE1 (z / ρ)) s = 1 / (s - ρ) + 1 / ρ := by
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : s / ρ ≠ 1 := fun h ↦ hs ((div_eq_one_iff_eq hρ).mp h)
  have h1ρ : (1 : ℂ) - s / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hu : HasDerivAt (fun z : ℂ ↦ z / ρ) (1 / ρ) s := by
    simpa using (hasDerivAt_id s).div_const ρ
  have hc : HasDerivAt (fun z ↦ weierstrassE1 (z / ρ))
      (-(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)) s := by
    have h := (hasDerivAt_weierstrassE1 (s / ρ)).comp s hu
    simpa [Function.comp_def] using h
  rw [logDeriv_apply, hc.deriv]
  simp only [weierstrassE1]
  rw [show -(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)
        = (-(s / ρ) * (1 / ρ)) * Complex.exp (s / ρ) by ring,
      mul_div_mul_right _ _ (Complex.exp_ne_zero _), div_eq_iff h1ρ]
  field_simp
  ring

/-- The partial-fraction terms `1/(s - ρᵢ) + 1/ρᵢ` are summable, for `s` not a nontrivial
zero. -/
theorem summable_partial_fraction {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ 1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  have hu : Summable (fun i ↦ 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * (‖s‖ + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (‖s‖ + 1))) ^ 2 := by positivity
    filter_upwards [hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [htail] with i hi
  have hρpos : 0 < ‖ρ i‖ := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  have hsρpos : 0 < ‖s - ρ i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs i))
  -- `‖ρ i‖ ≥ 2(‖s‖+1)`.
  have hbig : 2 * (‖s‖ + 1) ≤ ‖ρ i‖ := by
    rw [norm_inv, one_div] at hi
    exact (inv_le_inv₀ hρpos (by positivity)).mp hi
  -- reverse triangle inequality: `‖s - ρ i‖ ≥ ‖ρ i‖ - ‖s‖ ≥ ‖ρ i‖/2`.
  have hge : ‖ρ i‖ / 2 ≤ ‖s - ρ i‖ := by
    have h1 : ‖ρ i‖ - ‖s‖ ≤ ‖s - ρ i‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    nlinarith [norm_nonneg s]
  -- bound `‖(s - ρ i)⁻¹‖ ≤ 2‖(ρ i)⁻¹‖`.
  have hinv : ‖(s - ρ i)⁻¹‖ ≤ 2 * ‖(ρ i)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    rw [show 2 * ‖ρ i‖⁻¹ = (‖ρ i‖ / 2)⁻¹ by rw [inv_div]; ring]
    exact inv_anti₀ (by positivity) hge
  have hρi : ρ i ≠ 0 := riemannXiZeros_ne_zero i
  have hsρi : s - ρ i ≠ 0 := sub_ne_zero.mpr (hs i)
  have hterm : 1 / (s - ρ i) + 1 / ρ i = s * (ρ i)⁻¹ * (s - ρ i)⁻¹ := by
    field_simp
    ring
  calc ‖1 / (s - ρ i) + 1 / ρ i‖
      = ‖s‖ * ‖(ρ i)⁻¹‖ * ‖(s - ρ i)⁻¹‖ := by rw [hterm, norm_mul, norm_mul]
    _ ≤ ‖s‖ * ‖(ρ i)⁻¹‖ * (2 * ‖(ρ i)⁻¹‖) := by gcongr
    _ = 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2 := by ring

/-- **Logarithmic derivative of the canonical product.** Away from its zeros, the logarithmic
derivative of `P(s) = ∏ᵢ E₁(s/ρᵢ)` is the sum of the factor logarithmic derivatives. -/
theorem logDeriv_riemannXiCanonicalProduct_eq {s : ℂ}
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) s
      = ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i)
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hfne : ∀ i, f i s ≠ 0 := fun i ↦
    weierstrassE1_ne_zero (fun h ↦ hs i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h))
  have hlog : ∀ i, logDeriv (f i) s = 1 / (s - ρ i) + 1 / ρ i := fun i ↦
    logDeriv_weierstrassE1_div (riemannXiZeros_ne_zero i) (hs i)
  have hmsum : Summable (fun i ↦ logDeriv (f i) s) := by
    simp only [hlog]; exact summable_partial_fraction hs
  have htend : MultipliableLocallyUniformlyOn f Set.univ :=
    (hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ hsum).multipliableLocallyUniformlyOn
  have hnez : ∏' i, f i s ≠ 0 :=
    riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hs
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ s)
    hfne hd hmsum htend hnez
  exact hkey.trans (tsum_congr hlog)

/-- `ξ` is non-vanishing at any point that is not one of its enumerated zeros. -/
theorem riemannXi_ne_zero_of_forall_ne {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    riemannXi s ≠ 0 := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  rw [hB s]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
    (riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros
      summable_inv_norm_sq_riemannXiZeros hs)

/-- **Partial-fraction expansion of `ξ'/ξ`** (`lem:lb_pf_xi`). The constant `ξ'/ξ(0)` is the
Hadamard constant `B`. -/
theorem logDeriv_riemannXi_eq {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  -- At any non-zero point, `ξ'/ξ = B + ∑ᵢ (1/(s - ρᵢ) + 1/ρᵢ)`.
  have key : ∀ z : ℂ, (∀ i, z ≠ riemannXiZeros i) →
      logDeriv riemannXi z = B + ∑' i, (1 / (z - riemannXiZeros i) + 1 / riemannXiZeros i) := by
    intro z hz
    have hPne : riemannXiCanonicalProduct riemannXiZeros z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne _ summable_inv_norm_sq_riemannXiZeros hz
    have hξfun : riemannXi =
        fun w ↦ (1 / 2 * Complex.exp (B * w)) * riemannXiCanonicalProduct riemannXiZeros w := by
      funext w; rw [hB w]
    have hpre : (1 / 2 * Complex.exp (B * z) : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
    have hdpre : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * Complex.exp (B * w)) z := by
      fun_prop
    have hdP : DifferentiableAt ℂ (riemannXiCanonicalProduct riemannXiZeros) z :=
      differentiable_riemannXiCanonicalProduct _ summable_inv_norm_sq_riemannXiZeros z
    rw [hξfun, logDeriv_mul z hpre hPne hdpre hdP,
      logDeriv_riemannXiCanonicalProduct_eq hz]
    congr 1
    -- `logDeriv (½ exp(B·)) z = B`.
    rw [logDeriv_const_mul z _ (by norm_num)]
    have hde : HasDerivAt (fun w : ℂ ↦ Complex.exp (B * w)) (Complex.exp (B * z) * B) z := by
      simpa using ((hasDerivAt_id z).const_mul (B : ℂ)).cexp
    rw [logDeriv_apply, hde.deriv, mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero _),
      mul_one]
  -- Identify `B = ξ'/ξ(0)` by evaluating at `0`.
  have h0 : ∀ i, (0 : ℂ) ≠ riemannXiZeros i := fun i ↦ (riemannXiZeros_ne_zero i).symm
  have htsum0 : ∑' i, (1 / ((0 : ℂ) - riemannXiZeros i) + 1 / riemannXiZeros i) = 0 := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero]
  have hkey0 := key 0 h0
  rw [htsum0, add_zero] at hkey0
  rw [key s hs, hkey0]

/-- **The Davenport explicit formula for `ζ'/ζ`** (`lem:lb_pf_zeta`), with `ψ = Complex.digamma`
and `ξ'/ξ(0)` the constant of `logDeriv_riemannXi_eq`. -/
theorem logDeriv_riemannZeta_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannZeta s = logDeriv riemannXi 0 - 1 / s - 1 / (s - 1)
      + 1 / 2 * (Real.log π : ℂ) - 1 / 2 * Complex.digamma (s / 2)
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hre
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  -- `Re(s/2) > 0` and consequences for `Γ(s/2)`.
  have hsdiv : 0 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsdiv
  have hnp : ∀ m : ℕ, s / 2 ≠ -↑m := ne_neg_natCast_of_re_pos hsdiv
  have hdΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := differentiableAt_Gamma_of_re_pos hsdiv
  -- `ζ(s) ≠ 0` from `ξ(s) ≠ 0` and the factorisation.
  have hζne : riemannZeta s ≠ 0 := by
    intro h
    exact (riemannXi_ne_zero_of_forall_ne hs)
      (by rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓℝ, h, mul_zero])
  -- `logDeriv (π^{-·/2}) s = -½ log π`.
  have hcpowne : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hf : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).neg).div_const 2
  have hcp : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := hf.const_cpow (Or.inl hπ)
  have hlcpow : logDeriv (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) := by
    rw [logDeriv_apply, hcp.deriv,
      show (π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)
        = (Complex.log π * (-1 / 2)) * (π : ℂ) ^ (-s / 2) by ring,
      mul_div_assoc, div_self hcpowne, mul_one, ← Complex.ofReal_log Real.pi_pos.le]
    ring
  -- `logDeriv (Γ(·/2)) s = ½ ψ(s/2)`.
  have hu : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hdΓfun : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) s :=
    hdΓ.comp s hu.differentiableAt
  have hcomp : logDeriv (Complex.Gamma ∘ fun w : ℂ ↦ w / 2) s
      = logDeriv Complex.Gamma (s / 2) * deriv (fun w : ℂ ↦ w / 2) s :=
    logDeriv_comp hdΓ hu.differentiableAt
  have hlΓ : logDeriv (fun w : ℂ ↦ Complex.Gamma (w / 2)) s
      = (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    rw [show (fun w : ℂ ↦ Complex.Gamma (w / 2)) = Complex.Gamma ∘ fun w ↦ w / 2 from rfl,
      hcomp, hu.deriv, ← Complex.digamma_def]
    ring
  -- `logDeriv Γ_ℝ s = -½ log π + ½ ψ(s/2)`.
  have hdcpow : DifferentiableAt ℂ (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s := hcp.differentiableAt
  have hB' : logDeriv Gammaℝ s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2) := by
    rw [show (Gammaℝ : ℂ → ℂ) = fun w ↦ (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) from rfl,
      logDeriv_mul s hcpowne hΓne hdcpow hdΓfun, hlcpow, hlΓ]
  -- `logDeriv (½ w(w-1)) s = 1/s + 1/(s-1)`.
  have hA : logDeriv (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s = 1 / s + 1 / (s - 1) := by
    have hda : HasDerivAt (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) (1 / 2 * (1 * (s - 1) + s * 1)) s :=
      ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).const_mul (1 / 2)
    rw [logDeriv_apply, hda.deriv]
    field_simp
  -- Differentiability/non-vanishing for the elementary factorisation.
  have hdΓℝ : DifferentiableAt ℂ Gammaℝ s := (Complex.analyticAt_Gammaℝ hre).differentiableAt
  have hdA' : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s := by fun_prop
  have hdf1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w) s := hdA'.mul hdΓℝ
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hAne : (1 / 2 * (s * (s - 1)) : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hsm1)
  have hf1ne : (1 / 2 * (s * (s - 1)) * Gammaℝ s : ℂ) ≠ 0 := mul_ne_zero hAne hΓℝ
  -- `ξ = ½ s(s-1) Γ_ℝ ζ` on a neighbourhood of `s`.
  have hEq : riemannXi =ᶠ[nhds s]
      fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w := by
    have hV : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | w ≠ 1}) :=
      (Complex.isOpen_re_gt 0).inter isOpen_ne
    filter_upwards [hV.mem_nhds ⟨hre, hs1⟩] with w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hw0' : w ≠ 0 := by rintro rfl; simp at hw0
    exact riemannXi_eq_prefactor_mul hw0' hw1 (Gammaℝ_ne_zero_of_re_pos hw0)
  have hlogeq : logDeriv riemannXi s
      = logDeriv (fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
  -- Two expressions for `ξ'/ξ(s)`.
  have hxi1 : logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := logDeriv_riemannXi_eq hs
  have hxi2 : logDeriv riemannXi s = 1 / s + 1 / (s - 1)
      + (-(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2))
      + logDeriv riemannZeta s := by
    rw [hlogeq, logDeriv_mul s hf1ne hζne hdf1 hdζ, logDeriv_mul s hAne hΓℝ hdA' hdΓℝ, hA, hB']
  have heq := hxi2.symm.trans hxi1
  linear_combination heq

