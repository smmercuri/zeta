/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardConcrete
public import Zeta.Hadamard.HadamardProduct
public import Zeta.ArgZeta.PartialFraction
public import Zeta.ArgZeta.Booker
public import Zeta.Gamma.DigammaStirling
public import Zeta.RiemannXi
public import Zeta.RiemannVonMangoldt.Main
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The reflection symmetry of the zeros of `ξ`, and the shift-by-`d` log-modulus identity

The multiset of zeros of `ξ` is invariant under the reflection `ρ ↦ 1 - conj ρ` across the
critical line — the one place the functional equation enters Lehman's lower bound. Also the
shift-by-`d` log-modulus identity built on the Hadamard product, the summed booker bound it feeds,
and the log-`t` coefficient extracted from the explicit formula.

## Main results

* `analyticOrderAt_riemannXi_one_sub_conj`, `divisor_riemannXi_one_sub_conj`: the analytic order
  and the divisor of `ξ` are invariant under `z ↦ 1 - conj z`.
* `tsum_riemannXiZeros_one_sub_conj` (`lem:ll_reflection`): for any `g : ℂ → ℂ`,
  `∑' i, g (riemannXiZeros i) = ∑' i, g (1 - conj (riemannXiZeros i))`.
* `riemannXiZeros_re_pos`, `riemannXiZeros_re_lt_one`: every enumerated zero lies in the open
  critical strip `0 < Re ρᵢ < 1`.
* `exists_const_tsum_log_norm_riemannXiZeros_shift_eq` (`lem:ll_logabs_diff`): for a real constant
  `κ`, `∑ᵢ [log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] = log‖ξ(s+d)‖ - log‖ξ(s)‖ - dκ`, off the zeros.
* `integral_tsum_log_norm_shift_le_of` (`lem:ll_booker_sum`): the summed booker bound,
  `∑ᵢ ∫₀ᵈ [log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] ≤ c d² ∑ᵢ Re 1/(s_d - ρᵢ)` for any pairing constant `c ≥ 2`.
* `tsum_re_inv_riemannXiZeros_sub_le` (`lem:ll_zeta_sum`): `∑ᵢ Re 1/(s_d - ρᵢ) ≤ ½ log t + C`
  with `C` a `t`-independent constant.
-/
@[expose] public section


open Complex Filter Topology Function Set

open Complex.Stirling
open scoped Real

/-- The index type enumerating the zeros of `ξ` is countable. -/
instance : Countable RiemannXiZerosIndex := by
  have : Countable ↥(MeromorphicOn.divisor riemannXi ⊤).support :=
    ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (MeromorphicOn.divisor riemannXi ⊤).discreteSupport).to_subtype
  infer_instance

/-- **Schwarz reflection (analytic form).** If `g` is analytic at `conj u`, then the reflected
function `w ↦ conj (g (conj w))` is analytic at `u`. -/
theorem AnalyticAt.conj_conj {g : ℂ → ℂ} {u : ℂ}
    (hg : AnalyticAt ℂ g (starRingEnd ℂ u)) :
    AnalyticAt ℂ (fun w ↦ starRingEnd ℂ (g (starRingEnd ℂ w))) u := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Complex.continuous_conj.continuousAt.eventually
    (hg.eventually_analyticAt.mono fun y hy ↦ hy.differentiableAt)] with w hw
  simpa [Function.comp_def] using hw.conj_conj

/-- `ξ` is analytic at every point (being entire). -/
private theorem analyticAt_riemannXi (w : ℂ) : AnalyticAt ℂ riemannXi w :=
  differentiable_riemannXi.analyticAt w

/-- The analytic order of `ξ` is finite at every point, since `ξ` is not identically zero. -/
private theorem analyticOrderAt_riemannXi_ne_top (w : ℂ) :
    analyticOrderAt riemannXi w ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w analyticAt_riemannXi]
  intro h
  simpa [riemannXi_zero] using congrFun h 0

/-- The analytic order of `ξ` is invariant under conjugation. -/
theorem analyticOrderAt_riemannXi_conj (z : ℂ) :
    analyticOrderAt riemannXi (starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  set N := analyticOrderNatAt riemannXi z
  obtain ⟨g, hg, hg0, hfac⟩ :=
    (analyticAt_riemannXi z).analyticOrderAt_ne_top.mp (analyticOrderAt_riemannXi_ne_top z)
  have hgconj : AnalyticAt ℂ (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) :=
    AnalyticAt.conj_conj (u := starRingEnd ℂ z) (by rw [Complex.conj_conj]; exact hg)
  have hval : (fun u ↦ starRingEnd ℂ (g (starRingEnd ℂ u))) (starRingEnd ℂ z) ≠ 0 := by
    simp only [Complex.conj_conj]
    exact fun h ↦ hg0 (by simpa using congrArg (starRingEnd ℂ) h)
  have hfac2 : riemannXi =ᶠ[𝓝 (starRingEnd ℂ z)]
      fun u ↦ (u - starRingEnd ℂ z) ^ N • (starRingEnd ℂ (g (starRingEnd ℂ u))) := by
    have hc : ContinuousAt (starRingEnd ℂ) (starRingEnd ℂ z) :=
      Complex.continuous_conj.continuousAt
    have hpull : ∀ᶠ u in 𝓝 (starRingEnd ℂ z),
        riemannXi (starRingEnd ℂ u) = (starRingEnd ℂ u - z) ^ N • g (starRingEnd ℂ u) := by
      have hbase : ∀ᶠ y in 𝓝 (starRingEnd ℂ (starRingEnd ℂ z)),
          riemannXi y = (y - z) ^ N • g y := by rw [Complex.conj_conj]; exact hfac
      exact hc.eventually hbase
    filter_upwards [hpull] with u hu
    have h2 := congrArg (starRingEnd ℂ) hu
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, riemannXi_conj, Complex.conj_conj] at h2
    simpa only [smul_eq_mul] using h2
  have hcz : analyticOrderNatAt riemannXi (starRingEnd ℂ z) = N := by
    rw [(analyticAt_riemannXi (starRingEnd ℂ z)).analyticOrderNatAt_eq_iff
      (analyticOrderAt_riemannXi_ne_top _)]
    exact ⟨_, hgconj, hval, hfac2⟩
  rw [← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top (starRingEnd ℂ z)),
    ← Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannXi_ne_top z), hcz]

/-- The analytic order of `ξ` is invariant under the affine reflection `z ↦ 1 - z`. -/
theorem analyticOrderAt_riemannXi_one_sub (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have hcomp : analyticOrderAt (riemannXi ∘ fun w ↦ 1 - w) z
      = analyticOrderAt riemannXi ((fun w ↦ 1 - w) z) := by
    refine analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_const.sub analyticAt_id) ?_
    have hd : deriv (fun w : ℂ ↦ 1 - w) z = -1 := ((hasDerivAt_id z).const_sub (1 : ℂ)).deriv
    rw [hd]; exact neg_ne_zero.mpr one_ne_zero
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext w; simp only [comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  exact hcomp.symm

/-- The analytic order of `ξ` is invariant under the critical-line reflection `z ↦ 1 - conj z`. -/
theorem analyticOrderAt_riemannXi_one_sub_conj (z : ℂ) :
    analyticOrderAt riemannXi (1 - starRingEnd ℂ z) = analyticOrderAt riemannXi z := by
  rw [analyticOrderAt_riemannXi_one_sub, analyticOrderAt_riemannXi_conj]

/-- The divisor of `ξ` is invariant under the critical-line reflection `z ↦ 1 - conj z`. -/
theorem divisor_riemannXi_one_sub_conj (z : ℂ) :
    MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ z)
      = MeromorphicOn.divisor riemannXi ⊤ z := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  rw [divisor_eq_analyticOrderNatAt hf, divisor_eq_analyticOrderNatAt hf]
  simp only [analyticOrderNatAt, analyticOrderAt_riemannXi_one_sub_conj]

/-- **The reflection reindexing involution** underlying `lem:ll_reflection`: a self-inverse
bijection `e` of the zero-enumeration index type with
`riemannXiZeros (e i) = 1 - conj (riemannXiZeros i)`. -/
theorem exists_equiv_riemannXiZeros_one_sub_conj :
    ∃ e : RiemannXiZerosIndex ≃ RiemannXiZerosIndex,
      ∀ i, riemannXiZeros (e i) = 1 - starRingEnd ℂ (riemannXiZeros i) := by
  -- the reflection involution on the support of the divisor
  let F : (MeromorphicOn.divisor riemannXi ⊤).support →
      (MeromorphicOn.divisor riemannXi ⊤).support :=
    fun a ↦ ⟨1 - starRingEnd ℂ (a : ℂ), by
      rw [mem_support, divisor_riemannXi_one_sub_conj]
      exact mem_support.mp a.2⟩
  have hFinv : Involutive F := by
    intro a
    apply Subtype.ext
    change 1 - starRingEnd ℂ (1 - starRingEnd ℂ (a : ℂ)) = (a : ℂ)
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  let eSupp := hFinv.toPerm F
  -- the divisor fibres have equal cardinality at `a` and its reflection
  have hfib : ∀ a : (MeromorphicOn.divisor riemannXi ⊤).support,
      (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
        = (MeromorphicOn.divisor riemannXi ⊤ (eSupp a : ℂ)).toNat := by
    intro a
    change (MeromorphicOn.divisor riemannXi ⊤ (a : ℂ)).toNat
      = (MeromorphicOn.divisor riemannXi ⊤ (1 - starRingEnd ℂ (a : ℂ))).toNat
    rw [divisor_riemannXi_one_sub_conj]
  -- the involution of the index type
  refine ⟨Equiv.sigmaCongr eSupp (fun a ↦ finCongr (hfib a)), ?_⟩
  rintro ⟨a, k⟩
  rfl

/-- **Reflection reindexing of the zeros** (`lem:ll_reflection`). Summing any `g` over the zeros
of `ξ` is invariant under reflecting each zero `ρ` to `1 - conj ρ`. No summability is needed. -/
theorem tsum_riemannXiZeros_one_sub_conj {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    ∑' i, g (riemannXiZeros i) = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  calc ∑' i, g (riemannXiZeros i)
      = ∑' i, g (riemannXiZeros (e i)) := (e.tsum_eq (fun i ↦ g (riemannXiZeros i))).symm
    _ = ∑' i, g (1 - starRingEnd ℂ (riemannXiZeros i)) := by simp_rw [hval]

/-- **Summability is invariant under the reflection reindexing.** The family `i ↦ g(1 - conj ρᵢ)`
is summable iff `i ↦ g(ρᵢ)` is. -/
theorem summable_riemannXiZeros_one_sub_conj_iff {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (g : ℂ → M) :
    Summable (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      ↔ Summable (fun i ↦ g (riemannXiZeros i)) := by
  obtain ⟨e, hval⟩ := exists_equiv_riemannXiZeros_one_sub_conj
  have hcomp : (fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)))
      = (fun j ↦ g (riemannXiZeros j)) ∘ e := by
    ext i; simp only [Function.comp_apply, hval i]
  rw [hcomp, Equiv.summable_iff]

/-! ## The shift-by-`d` log-modulus identity (`lem:ll_logabs_diff`) -/

/-- Each enumerated zero is genuinely a zero of `ξ`: `ξ(ρᵢ) = 0`. -/
theorem riemannXi_riemannXiZeros_eq_zero (i : RiemannXiZerosIndex) :
    riemannXi (riemannXiZeros i) = 0 := by
  have hf : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (riemannXiZeros i) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [divisor_eq_analyticOrderNatAt hf] at hmem
  have hnat : analyticOrderNatAt riemannXi (riemannXiZeros i) ≠ 0 := by
    intro h; rw [h] at hmem; simp at hmem
  have hAt : AnalyticAt ℂ riemannXi (riemannXiZeros i) := differentiable_riemannXi.analyticAt _
  rw [← hAt.analyticOrderAt_ne_zero]
  intro hz
  exact hnat (by simp [analyticOrderNatAt, hz])

/-- Every enumerated zero has real part `> 0` (it lies in the critical strip). -/
theorem riemannXiZeros_re_pos (i : RiemannXiZerosIndex) : 0 < (riemannXiZeros i).re :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).1

/-- Every enumerated zero has real part `< 1` (it lies in the critical strip). -/
theorem riemannXiZeros_re_lt_one (i : RiemannXiZerosIndex) : (riemannXiZeros i).re < 1 :=
  (riemannXi_re_mem_Ioo_of_eq_zero (riemannXi_riemannXiZeros_eq_zero i)).2

/-- `|Re(ρ⁻¹)| ≤ ‖ρ⁻¹‖²` for `ρ` in the open critical strip `0 < Re ρ < 1`. -/
private lemma abs_re_inv_le_norm_sq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    |(ρ⁻¹).re| ≤ ‖ρ⁻¹‖ ^ 2 := by
  have hne : ρ ≠ 0 := fun h ↦ by rw [h] at h0; simp at h0
  have hns : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hne
  have hsq : ‖ρ⁻¹‖ ^ 2 = (Complex.normSq ρ)⁻¹ := by rw [norm_inv, inv_pow, Complex.sq_norm]
  rw [Complex.inv_re, hsq, abs_div, abs_of_pos h0, abs_of_pos hns, div_le_iff₀ hns,
    inv_mul_cancel₀ (ne_of_gt hns)]
  exact h1.le

/-- The real parts `Re(1/ρᵢ)` are summable, dominated by `∑ᵢ |ρᵢ|⁻²`. -/
theorem summable_re_inv_riemannXiZeros :
    Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := by
  refine Summable.of_norm_bounded summable_inv_norm_sq_riemannXiZeros (fun i ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_re_inv_le_norm_sq (riemannXiZeros_re_pos i) (riemannXiZeros_re_lt_one i)

/-- Log-modulus of the genus-one factor argument: for `ρ ≠ 0` and `w ≠ ρ`,
`log‖1 - w/ρ‖ = log‖w - ρ‖ - log‖ρ‖`. -/
private lemma log_norm_one_sub_div {ρ : ℂ} (hρ : ρ ≠ 0) {w : ℂ} (hw : w ≠ ρ) :
    Real.log ‖1 - w / ρ‖ = Real.log ‖w - ρ‖ - Real.log ‖ρ‖ := by
  have hh : (1 : ℂ) - w / ρ = (ρ - w) / ρ := by rw [sub_div, div_self hρ]
  rw [hh, norm_div, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦ hw h.symm))
    (norm_ne_zero_iff.mpr hρ), norm_sub_rev]

/-- **Shift-by-`d` log-modulus identity** (`lem:ll_logabs_diff`). There is a real constant
`κ = B + ∑ᵢ Re(1/ρᵢ)` (with `B` the Hadamard constant) such that, for every `s` not a zero of `ξ`
and with `s + d` not a zero,
`∑ᵢ [log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] = log‖ξ(s+d)‖ - log‖ξ(s)‖ - dκ`. -/
theorem exists_const_tsum_log_norm_riemannXiZeros_shift_eq :
    ∃ κ : ℝ, ∀ (s : ℂ) (d : ℝ), (∀ i, s ≠ riemannXiZeros i) →
        (∀ i, s + d ≠ riemannXiZeros i) →
        ∑' i, (Real.log ‖s + d - riemannXiZeros i‖ - Real.log ‖s - riemannXiZeros i‖)
          = Real.log ‖riemannXi (s + d)‖ - Real.log ‖riemannXi s‖ - d * κ := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have hsum : Summable fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2 := summable_inv_norm_sq_riemannXiZeros
  have hresum : Summable fun i ↦ ((riemannXiZeros i)⁻¹).re := summable_re_inv_riemannXiZeros
  refine ⟨B + ∑' i, ((riemannXiZeros i)⁻¹).re, fun s d hs hsd ↦ ?_⟩
  set ρ := riemannXiZeros
  -- The genus-one factor argument `z/ρᵢ` avoids its unique zero at `1`.
  have hzne : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) → ∀ i, z / ρ i ≠ 1 := fun {z} hz i h ↦
    hz i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h)
  -- The split family `i ↦ log‖1-z/ρᵢ‖ + Re(z/ρᵢ)` (`= log‖E₁(z/ρᵢ)‖`) is summable.
  have hsummSplit : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Summable (fun i ↦ Real.log ‖1 - z / ρ i‖ + (z / ρ i).re) := fun {z} hz ↦
    (summable_log_norm_weierstrassE1 ρ hsum z).congr
      (fun i ↦ log_norm_weierstrassE1 (hzne hz i))
  -- `log‖ξ z‖ = log(1/2) + B·Re z + log‖P z‖` for `z` not a zero.
  have hlogXi : ∀ {z : ℂ}, (∀ i, z ≠ ρ i) →
      Real.log ‖riemannXi z‖
        = Real.log (1 / 2) + B * z.re + Real.log ‖riemannXiCanonicalProduct ρ z‖ := by
    intro z hz
    have hPne : riemannXiCanonicalProduct ρ z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hz
    have h12 : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [norm_div, norm_one, Complex.norm_ofNat]
    rw [hB z, norm_mul, norm_mul, Complex.norm_exp, h12,
      show ((B : ℂ) * z).re = B * z.re from by rw [Complex.re_ofReal_mul],
      Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hPne),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  -- The `ξ`-difference in terms of the canonical product.
  have hdiffXi : Real.log ‖riemannXi (s + ↑d)‖ - Real.log ‖riemannXi s‖
      = B * d + (Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖) := by
    rw [hlogXi hsd, hlogXi hs, Complex.add_re, Complex.ofReal_re]; ring
  -- Per-term: `(aᵢ - bᵢ) = Dᵢ + d·Re(1/ρᵢ)`.
  have hterm : ∀ i,
      (Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re)
        = (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) + d * ((ρ i)⁻¹).re := by
    intro i
    have hρ0 := riemannXiZeros_ne_zero i
    have hsubdiv : (s + ↑d) / ρ i - s / ρ i = (↑d : ℂ) * (ρ i)⁻¹ := by
      rw [div_sub_div_same, add_sub_cancel_left, div_eq_mul_inv]
    have ere : ((s + ↑d) / ρ i).re - (s / ρ i).re = d * ((ρ i)⁻¹).re := by
      rw [← Complex.sub_re, hsubdiv, Complex.re_ofReal_mul]
    rw [log_norm_one_sub_div hρ0 (hsd i), log_norm_one_sub_div hρ0 (hs i)]
    linear_combination ere
  -- `∑(aᵢ-bᵢ) = ∑Dᵢ + d·∑Re(1/ρᵢ)`.
  have hsplit : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = ∑' i, (Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖)
          + d * ∑' i, ((ρ i)⁻¹).re := by
    have hD : Summable (fun i ↦ Real.log ‖s + ↑d - ρ i‖ - Real.log ‖s - ρ i‖) := by
      refine ((hsummSplit hsd).sub (hsummSplit hs)).sub (hresum.mul_left d) |>.congr fun i ↦ ?_
      rw [hterm i]; ring
    rw [funext (fun i ↦ hterm i), hD.tsum_add (hresum.mul_left d), tsum_mul_left]
  -- `∑(aᵢ-bᵢ) = log‖P(s+d)‖ - log‖P s‖`.
  have hPsub : ∑' i, ((Real.log ‖1 - (s + ↑d) / ρ i‖ + ((s + ↑d) / ρ i).re)
          - (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re))
      = Real.log ‖riemannXiCanonicalProduct ρ (s + ↑d)‖
          - Real.log ‖riemannXiCanonicalProduct ρ s‖ := by
    rw [(hsummSplit hsd).tsum_sub (hsummSplit hs),
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hsd,
      ← log_norm_riemannXiCanonicalProduct_eq_tsum ρ hsum hs]
  rw [hPsub] at hsplit
  rw [hdiffXi]
  linarith [hsplit]

/-! ## The summed booker bound (`lem:ll_booker_sum`) -/

/-- The integrand of Lehman's shift-difference: along the vertical line `s = 1/2 + x + i t`, the
difference `log‖s + d - ρ‖ - log‖s - ρ‖` of log-moduli to the zero `ρ` and its horizontal
`d`-shift. -/
noncomputable def shiftLogIntegrand (t d : ℝ) (ρ : ℂ) (x : ℝ) : ℝ :=
    Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ‖
      - Real.log ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ‖

/-- The shift-difference integral `∫₀ᵈ [log‖s+d-ρ‖ - log‖s-ρ‖] dx` of `shiftLogIntegrand`. -/
noncomputable def shiftLogIntegral (t d : ℝ) (ρ : ℂ) : ℝ :=
    ∫ x in (0 : ℝ)..d, shiftLogIntegrand t d ρ x

/-- Quadratic control of the log-modulus of the genus-one factor: for `‖z‖ ≤ 1/2`,
`|log‖1 - z‖ + Re z| ≤ ‖z‖²`. -/
private lemma abs_log_norm_one_sub_add_re_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 - z‖ + z.re| ≤ ‖z‖ ^ 2 := by
  have h : Real.log ‖1 - z‖ + z.re = (Complex.log (1 - z) + z).re := by
    rw [Complex.add_re, Complex.log_re]
  rw [h]
  exact (Complex.abs_re_le_norm _).trans (Complex.norm_log_one_sub_add_self_le hz)

/-- Quadratic control of the elementary factor along a bounded argument: if `‖z‖ ≤ C` and
`C‖ρ⁻¹‖ ≤ 1/2`, then `|log‖1 - z/ρ‖ + Re(z/ρ)| ≤ C²‖ρ⁻¹‖²`. -/
private lemma abs_log_norm_one_sub_div_add_re_le {z ρ : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C)
    (hsmall : C * ‖ρ⁻¹‖ ≤ 1 / 2) :
    |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by
  have hle : ‖z / ρ‖ ≤ C * ‖ρ⁻¹‖ := by
    rw [norm_div, norm_inv, div_eq_mul_inv]; gcongr
  calc |Real.log ‖1 - z / ρ‖ + (z / ρ).re| ≤ ‖z / ρ‖ ^ 2 :=
        abs_log_norm_one_sub_add_re_le (hle.trans hsmall)
    _ ≤ (C * ‖ρ⁻¹‖) ^ 2 := by gcongr
    _ = C ^ 2 * ‖ρ⁻¹‖ ^ 2 := by ring

/-- A point `z` with `Im z = t` differs from any `c` with `Im c ≠ t`: `z - c ≠ 0`. -/
private lemma sub_ne_zero_of_im_eq {z c : ℂ} {t : ℝ} (hz : z.im = t) (hc : c.im ≠ t) :
    z - c ≠ 0 := fun h ↦ hc (by
  have := congrArg Complex.im h
  rw [Complex.sub_im, hz, Complex.zero_im, sub_eq_zero] at this
  exact this.symm)

/-- The imaginary part of a point `1/2 + a + b·I` on a vertical line is `b`. -/
private lemma complex_line_im (a b : ℝ) : ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).im = b := by
  simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

/-- The real part of a point `1/2 + a + b·I` on a vertical line is `1/2 + a`. -/
private lemma complex_line_re (a b : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I).re = 1 / 2 + a := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]

/-- The imaginary part of the shifted point `1/2 + a + b·I + c` is `b`. -/
private lemma complex_line_add_im (a b c : ℝ) :
    ((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I + (c : ℂ)).im = b := by
  rw [Complex.add_im, complex_line_im, Complex.ofReal_im, add_zero]

/-- The genus-one decomposition of the shift-difference integrand: away from the zero `ρ`,
`log‖s+d-ρ‖ - log‖s-ρ‖ = E((s+d)/ρ) - E(s/ρ) - d·Re(ρ⁻¹)` with `E(z) = log‖1-z‖ + Re z` and
`s = 1/2 + x + i t`. The counterterm `d·Re(ρ⁻¹)` is what makes the difference `O(|ρ|⁻²)`. -/
private lemma shiftLogIntegrand_eq {ρ : ℂ} (hρ : ρ ≠ 0) (t d x : ℝ)
    (h1 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ)
    (h2 : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ) :
    shiftLogIntegrand t d ρ x
      = ((Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re)
          - (Real.log ‖1 - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ‖
            + (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re))
        - d * (ρ⁻¹).re := by
  have ere : (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ).re
      - (((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ).re = d * (ρ⁻¹).re := by
    rw [← Complex.sub_re,
      show ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)) / ρ
          - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) / ρ = (d : ℂ) * ρ⁻¹ by
        rw [div_sub_div_same,
          show (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)
              - ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) = (d : ℂ) by ring,
          div_eq_mul_inv],
      Complex.re_ofReal_mul]
  unfold shiftLogIntegrand
  rw [log_norm_one_sub_div hρ h1, log_norm_one_sub_div hρ h2]
  linear_combination -ere

/-- The shift-difference integrand is continuous in `x`, for a zero `ρ` of ordinate `≠ t`. -/
private lemma continuous_shiftLogIntegrand {ρ : ℂ} (t d : ℝ) (hρt : ρ.im ≠ t) :
    Continuous (shiftLogIntegrand t d ρ) := by
  unfold shiftLogIntegrand
  refine Continuous.sub (Continuous.log (by fun_prop) (fun x ↦ ?_))
    (Continuous.log (by fun_prop) (fun x ↦ ?_))
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ))
      (complex_line_add_im x t d) hρt
  · rw [norm_ne_zero_iff]
    exact sub_ne_zero_of_im_eq (z := (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I)
      (complex_line_im x t) hρt

/-- **The booker integrand is the sum of two shift-differences.** With `w = ρ - (1/2 + it)` and
`ρ* = 1 - conj ρ` the reflected zero, Lehman's booker integrand is
`[log‖s+d-ρ‖ - log‖s-ρ‖] + [log‖s+d-ρ*‖ - log‖s-ρ*‖]`. -/
private lemma bookerIntegrand_eq_shiftLog (ρ : ℂ) (t d x : ℝ) (hρt : ρ.im ≠ t) :
    Real.log ‖((x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))
        / (((x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
            * ((x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))))‖
      = shiftLogIntegrand t d ρ x + shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ) x := by
  -- the four conjugation identities `fᵢ = conj Aᵢ`
  have hc1 : (x : ℂ) + (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ)
        ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc2 : (x : ℂ) + (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) - ρ) := by
    apply Complex.ext <;> simp; ring
  have hc3 : (x : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
    apply Complex.ext <;> simp <;> ring
  have hc4 : (x : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
      = (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I - ρ) := by
    apply Complex.ext <;> simp; ring
  -- the four arguments are nonzero (imaginary part `t - Im ρ ≠ 0`)
  have him : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I).im = t := complex_line_im x t
  have himd : ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)).im = t := complex_line_add_im x t d
  have hρstar : (1 - (starRingEnd ℂ) ρ).im ≠ t := by
    simpa [Complex.sub_im, Complex.one_im, Complex.conj_im] using hρt
  have hA1 := sub_ne_zero_of_im_eq himd hρstar
  have hA2 := sub_ne_zero_of_im_eq himd hρt
  have hA3 := sub_ne_zero_of_im_eq him hρstar
  have hA4 := sub_ne_zero_of_im_eq him hρt
  rw [norm_div, norm_mul, norm_mul, hc1, hc2, hc3, hc4, Complex.norm_conj, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj,
    Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2))
      (mul_ne_zero (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)),
    Real.log_mul (norm_ne_zero_iff.mpr hA1) (norm_ne_zero_iff.mpr hA2),
    Real.log_mul (norm_ne_zero_iff.mpr hA3) (norm_ne_zero_iff.mpr hA4)]
  unfold shiftLogIntegrand
  ring

/-- **Per-zero booker pairing bound** (`lem:lb_booker` at the zero `ρ` and its reflection
`ρ* = 1 - conj ρ`), parametric in the pairing constant `c ≥ 2`:
`∫₀ᵈ[…ρ…] + ∫₀ᵈ[…ρ*…] ≤ c·d²(Re 1/(s_d-ρ) + Re 1/(s_d-ρ*))` at `s_d = 1/2 + d + it`. -/
private lemma shiftLogIntegral_add_le_of {ρ : ℂ} (t : ℝ) {d : ℝ} (hd : 1 / 2 < d)
    (hρt : ρ.im ≠ t) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {c : ℝ} (hc : 2 ≤ c) :
    shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ)
      ≤ c * d ^ 2 * ((((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re) := by
  have hwre : |(ρ - (1 / 2 + (t : ℂ) * I)).re| ≤ 1 / 2 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).re = ρ.re - 1 / 2 by simp]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hwim : (ρ - (1 / 2 + (t : ℂ) * I)).im ≠ 0 := by
    rw [show (ρ - (1 / 2 + (t : ℂ) * I)).im = ρ.im - t by simp]
    exact sub_ne_zero.mpr hρt
  have hbk := bookerPairIntegral_le_of hd hwre hwim hc
  -- residue identities (R)
  have hresPlus : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    have hc : (d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  have hresMinus : (1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re := by
    have hc : (d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I))
        = (starRingEnd ℂ) ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ) := by
      apply Complex.ext <;> simp; ring
    rw [one_div, hc, ← map_inv₀, Complex.conj_re]
  -- integrability of the two shift integrands
  have hI1 : IntervalIntegrable (shiftLogIntegrand t d ρ) MeasureTheory.volume 0 d :=
    (continuous_shiftLogIntegrand t d hρt).intervalIntegrable 0 d
  have hI2 : IntervalIntegrable (shiftLogIntegrand t d (1 - (starRingEnd ℂ) ρ))
      MeasureTheory.volume 0 d := by
    refine (continuous_shiftLogIntegrand t d ?_).intervalIntegrable 0 d
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
    exact hρt
  -- rewrite booker's LHS as the sum of the two shift integrals, and its RHS as the density sum
  have hLHS : bookerPairIntegral d (ρ - (1 / 2 + (t : ℂ) * I))
      = shiftLogIntegral t d ρ + shiftLogIntegral t d (1 - (starRingEnd ℂ) ρ) := by
    rw [bookerPairIntegral, shiftLogIntegral, shiftLogIntegral,
      ← intervalIntegral.integral_add hI1 hI2]
    exact intervalIntegral.integral_congr (fun x _ ↦ bookerIntegrand_eq_shiftLog ρ t d x hρt)
  have hRHS : (1 / ((d : ℂ) + (ρ - (1 / 2 + (t : ℂ) * I)))
        + 1 / ((d : ℂ) - (starRingEnd ℂ) (ρ - (1 / 2 + (t : ℂ) * I)))).re
      = (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - ρ)⁻¹).re
          + (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - (1 - (starRingEnd ℂ) ρ))⁻¹).re := by
    rw [Complex.add_re, hresPlus, hresMinus]; ring
  rw [hLHS, hRHS] at hbk
  exact hbk

/-- A crude norm bound on the abscissa point `1/2 + a + i b`: `‖1/2 + a + bi‖ ≤ 1/2 + |a| + |b|`. -/
lemma Complex.norm_complex_line_le (a b : ℝ) :
    ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖ ≤ 1 / 2 + |a| + |b| := by
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  calc ‖(1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I‖
      ≤ ‖(1 / 2 : ℂ) + (a : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_add_le _ _
    _ ≤ (‖(1 / 2 : ℂ)‖ + ‖(a : ℂ)‖) + ‖(b : ℂ) * I‖ := by gcongr; exact norm_add_le _ _
    _ = 1 / 2 + |a| + |b| := by
        rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]

/-- The real parts `Re 1/(s - ρᵢ)` of the shifted pairing density are summable off the zeros. -/
theorem summable_re_inv_riemannXiZeros_sub {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re) := by
  have h2 : Summable (fun i ↦ (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i).re) :=
    (summable_partial_fraction hs).map (Complex.reCLM : ℂ →L[ℝ] ℝ).toAddMonoidHom
      Complex.continuous_re
  refine (h2.sub summable_re_inv_riemannXiZeros).congr (fun i ↦ ?_)
  rw [Complex.add_re, one_div, one_div, add_sub_cancel_right]

/-- **A zero-free ordinate exists** (`lem:le_good_ordinate`). There is a real `t₀` with
`(ρᵢ).im ≠ t₀` for every index `i`. -/
theorem exists_forall_riemannXiZeros_im_ne :
    ∃ t₀ : ℝ, ∀ i, (riemannXiZeros i).im ≠ t₀ := by
  have hcount : (Set.range (fun i ↦ (riemannXiZeros i).im)).Countable := Set.countable_range _
  have hne : Set.range (fun i ↦ (riemannXiZeros i).im) ≠ Set.univ := fun h ↦
    Cardinal.not_countable_real (h ▸ hcount)
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_compl.mpr hne
  exact ⟨t₀, fun i h ↦ ht₀ ⟨i, h⟩⟩

/-- **Reflected zero sum cancels on the critical line** (`lem:le_refl_sum_zero`). If `s₀`
satisfies `conj s₀ = 1 - s₀` (i.e. `Re s₀ = 1/2`), then `∑ᵢ Re(1/(s₀ - ρᵢ)) = 0`. -/
theorem tsum_re_inv_riemannXiZeros_sub_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re = 0 := by
  have hgpt : ∀ z : ℂ, ((s₀ - (1 - starRingEnd ℂ z))⁻¹).re = -((s₀ - z)⁻¹).re := by
    intro z
    have hid : s₀ - (1 - starRingEnd ℂ z) = -(starRingEnd ℂ (s₀ - z)) := by
      rw [map_sub, hconj]; ring
    rw [hid, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
  have hcalc : (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
      = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re :=
    calc (∑' i, ((s₀ - riemannXiZeros i)⁻¹).re)
        = ∑' i, ((s₀ - (1 - starRingEnd ℂ (riemannXiZeros i)))⁻¹).re :=
          tsum_riemannXiZeros_one_sub_conj (fun z ↦ ((s₀ - z)⁻¹).re)
      _ = ∑' i, (-((s₀ - riemannXiZeros i)⁻¹).re) := by simp_rw [hgpt]
      _ = - ∑' i, ((s₀ - riemannXiZeros i)⁻¹).re := tsum_neg
  linarith

/-- `ξ'(conj s) = conj(ξ'(s))`. -/
private lemma deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (deriv riemannXi s) := by
  have hsym : starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have h : starRingEnd ℂ ∘ deriv riemannXi ∘ starRingEnd ℂ = deriv riemannXi := by
    rw [← deriv_conj_conj, hsym]
  simpa using congrArg (starRingEnd ℂ) (congrFun h s)

/-- `ξ'(1 - s) = -ξ'(s)`. -/
private lemma deriv_riemannXi_one_sub (s : ℂ) :
    deriv riemannXi (1 - s) = - deriv riemannXi s := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (riemannXi ∘ fun w ↦ 1 - w) (deriv riemannXi (1 - s) * (-1)) s :=
    ((differentiable_riemannXi (1 - s)).hasDerivAt).comp s hu
  have hfun : (riemannXi ∘ fun w ↦ 1 - w) = riemannXi := by
    funext z; simp only [Function.comp_apply, riemannXi_one_sub]
  rw [hfun] at hcomp
  have hd : HasDerivAt riemannXi (deriv riemannXi s) s := (differentiable_riemannXi s).hasDerivAt
  linear_combination -(hcomp.unique hd)

/-- **The logarithmic derivative of `ξ` is imaginary on the critical line**
(`lem:le_re_logderiv_zero`): if `conj s₀ = 1 - s₀` (i.e. `Re s₀ = 1/2`), then
`Re(ξ'/ξ(s₀)) = 0`. -/
theorem re_logDeriv_riemannXi_critical_eq_zero {s₀ : ℂ}
    (hconj : starRingEnd ℂ s₀ = 1 - s₀) :
    (logDeriv riemannXi s₀).re = 0 := by
  have ha : logDeriv riemannXi (starRingEnd ℂ s₀) = starRingEnd ℂ (logDeriv riemannXi s₀) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]
  have hb : logDeriv riemannXi (1 - s₀) = - logDeriv riemannXi s₀ := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]
  have hcomb : starRingEnd ℂ (logDeriv riemannXi s₀) = - logDeriv riemannXi s₀ := by
    rw [← ha, hconj, hb]
  have := congrArg Complex.re hcomb
  rw [Complex.conj_re, Complex.neg_re] at this
  linarith

/-- The real part of the partial-fraction series splits into the shifted pairing sum and the zero
sum: `Re(∑ᵢ [1/(s-ρᵢ) + 1/ρᵢ]) = ∑ᵢ Re 1/(s-ρᵢ) + ∑ᵢ Re 1/ρᵢ`, for `s` off the zeros. -/
private lemma re_tsum_partialFraction_add {s : ℂ} (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable fun i ↦ ((s - riemannXiZeros i)⁻¹).re) :
    (∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i)).re
      = ∑' i, ((s - riemannXiZeros i)⁻¹).re + ∑' i, ((riemannXiZeros i)⁻¹).re := by
  rw [Complex.re_tsum (summable_partial_fraction hsne),
    tsum_congr (fun i ↦ by rw [Complex.add_re, one_div, one_div]),
    hPair.tsum_add summable_re_inv_riemannXiZeros]

/-- **The reflection constant `κ` vanishes** (`lem:le_kappa_zero`). The Hadamard constant
`B = Re(ξ'/ξ(0))` and the zero sum `∑ᵢ Re(1/ρᵢ)` cancel. -/
theorem hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero :
    (logDeriv riemannXi 0).re + ∑' i, ((riemannXiZeros i)⁻¹).re = 0 := by
  obtain ⟨t₀, ht₀⟩ := exists_forall_riemannXiZeros_im_ne
  set s₀ : ℂ := (1 / 2 : ℂ) + (t₀ : ℂ) * I with hs₀
  have hs0im : s₀.im = t₀ := by rw [hs₀]; simp
  have hsne : ∀ i, s₀ ≠ riemannXiZeros i := fun i h ↦ ht₀ i (by rw [← h, hs0im])
  have hconj : starRingEnd ℂ s₀ = 1 - s₀ := by
    rw [hs₀]; apply Complex.ext <;> simp; ring
  have hkey := congrArg Complex.re (logDeriv_riemannXi_eq hsne)
  rw [Complex.add_re,
    re_tsum_partialFraction_add hsne (summable_re_inv_riemannXiZeros_sub hsne),
    re_logDeriv_riemannXi_critical_eq_zero hconj,
    tsum_re_inv_riemannXiZeros_sub_critical_eq_zero hconj, zero_add] at hkey
  linarith

/-- **Real part of the Davenport explicit formula, solved for the zero sum.** For `0 < Re s`,
`s ≠ 1` not a zero of `ξ`, with the pairing density summable,
`∑ᵢ Re 1/(s - ρᵢ) = Re(ζ'/ζ(s)) + Re(1/s) + Re(1/(s-1)) - ½ log π + ½ Re ψ(s/2)`. -/
theorem tsum_re_inv_riemannXiZeros_sub_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hsne : ∀ i, s ≠ riemannXiZeros i)
    (hPair : Summable (fun i ↦ ((s - riemannXiZeros i)⁻¹).re)) :
    ∑' i, ((s - riemannXiZeros i)⁻¹).re
      = (logDeriv riemannZeta s).re + (1 / s).re + (1 / (s - 1)).re
        - 1 / 2 * Real.log π + 1 / 2 * (Complex.digamma (s / 2)).re := by
  have hkey := logDeriv_riemannZeta_eq hre hs1 hsne
  have hκ := hadamardConst_add_tsum_re_inv_riemannXiZeros_eq_zero
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hlogpi_re : ((1 / 2 : ℂ) * (Real.log π : ℂ)).re = 1 / 2 * Real.log π := by
    rw [hhalf, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpsi_re : ((1 / 2 : ℂ) * Complex.digamma (s / 2)).re
      = 1 / 2 * (Complex.digamma (s / 2)).re := by rw [hhalf, Complex.re_ofReal_mul]
  have hexp := congrArg Complex.re hkey
  simp only [Complex.add_re, Complex.sub_re, hlogpi_re, hpsi_re] at hexp
  rw [re_tsum_partialFraction_add hsne hPair] at hexp
  linarith [hexp, hκ]

/-- **Summability of the pairing density** `i ↦ Re 1/(s_d - ρᵢ)` at the abscissa
`s_d = 1/2 + d + it` (`d > 1/2`). -/
lemma summable_pairDensity {t d : ℝ} (hd : 1 / 2 < d) :
    Summable (fun i ↦ (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re) :=
  summable_re_inv_riemannXiZeros_sub fun i h ↦ by
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, complex_line_re d t] at hlt; linarith

/-- Concavity bound `log (u + t) ≤ log t + u/t` for `0 ≤ u`, `0 < t`. -/
lemma Real.log_add_le {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    Real.log (u + t) ≤ Real.log t + u / t := by
  have hdiv : Real.log ((t + u) / t) ≤ u / t := by
    calc Real.log ((t + u) / t)
        ≤ (t + u) / t - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) ht)
      _ = u / t := by field_simp; ring
  rw [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < t + u)) ht.ne'] at hdiv
  rw [add_comm u t]
  linarith

/-- `Re(1/w) ≤ ‖w‖⁻¹` for any complex `w`. -/
lemma Complex.re_one_div_le_norm_inv (w : ℂ) : (1 / w).re ≤ ‖w‖⁻¹ := by
  rw [one_div]; exact (Complex.re_le_norm _).trans_eq (norm_inv w)

/-- `Re(1/z) ≤ 1` as soon as `‖z‖ ≥ 1`. -/
lemma Complex.one_div_re_le_one {z : ℂ} (hz : 1 ≤ ‖z‖) : (1 / z).re ≤ 1 :=
  (Complex.re_one_div_le_norm_inv z).trans ((inv_le_one₀ (by linarith)).2 hz)

/-- **Common setup for the shifted-abscissa zero-sum witnesses.** For `1/2 < d` and `0 < t`, at
`s = 1/2 + d + it`: the coordinates `Re s = 1/2 + d`, `Im s = t`, the positivity `Re s > 0` and
`Re s > 1`, the explicit-formula side conditions `s ≠ 1` and `s ≠ ρᵢ`, and the norm bounds
`1/2 + d ≤ ‖s‖`, `‖s‖ > 0`, `‖s‖ ≤ (1/2 + d) + t`. -/
lemma shiftedLine_setup {d t : ℝ} (hdlt : 1 / 2 < d) (ht0 : 0 < t) :
    ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d ∧
      ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t ∧
      0 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      1 < ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re ∧
      (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ 1 ∧
      (∀ i, (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I ≠ riemannXiZeros i) ∧
      1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      0 < ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ∧
      ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ ≤ (1 / 2 + d) + t := by
  have hsre : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).re = 1 / 2 + d := complex_line_re d t
  have hsim : ((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I).im = t := complex_line_im d t
  have hsnorm_lb : 1 / 2 + d ≤ ‖(1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I‖ := by
    rw [← hsre]; exact Complex.re_le_norm _
  refine ⟨hsre, hsim, ?_, ?_, ?_, ?_, hsnorm_lb, lt_of_lt_of_le (by linarith) hsnorm_lb, ?_⟩
  · rw [hsre]; linarith
  · rw [hsre]; linarith
  · intro h; rw [h] at hsim; simp at hsim; linarith
  · intro i h
    have hlt := riemannXiZeros_re_lt_one i
    rw [← h, hsre] at hlt; linarith
  · have h := Complex.norm_complex_line_le d t
    rw [abs_of_pos (by linarith : (0 : ℝ) < d), abs_of_pos ht0] at h
    linarith

/-- A triple triangle inequality `|a - b - c| ≤ |a| + |b| + |c|`. -/
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, le_abs_self b, le_abs_self c],
              by linarith [le_abs_self a, neg_abs_le b, neg_abs_le c]⟩

/-- **Eventual `O(|ρᵢ|⁻²)` bound for the shift integrand**:
`‖shiftLogIntegrand t d ρᵢ x‖ ≤ C‖ρᵢ⁻¹‖²` for `x ∈ (0,d]` and cofinitely many `i`. -/
private lemma exists_eventually_forall_norm_shiftLogIntegrand_le {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in Filter.cofinite, ∀ x ∈ Set.uIoc (0 : ℝ) d,
      ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
  have hd0 : (0 : ℝ) < d := by linarith
  set C0 : ℝ := 1 / 2 + 2 * d + |t| with hC0
  have hC0pos : 0 ≤ C0 := by rw [hC0]; positivity
  have hsum2 := summable_inv_norm_sq_riemannXiZeros
  have htail : ∀ᶠ i in Filter.cofinite, ‖(riemannXiZeros i)⁻¹‖ ≤ 1 / (2 * (C0 + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (C0 + 1))) ^ 2 := by positivity
    filter_upwards [hsum2.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine ⟨2 * C0 ^ 2 + d, by positivity, ?_⟩
  filter_upwards [htail] with i hi
  set ρ := riemannXiZeros i with hρ
  have hρ0 : ρ ≠ 0 := riemannXiZeros_ne_zero i
  have hρre0 : 0 < ρ.re := riemannXiZeros_re_pos i
  have hρre1 : ρ.re < 1 := riemannXiZeros_re_lt_one i
  have hsmall : C0 * ‖ρ⁻¹‖ ≤ 1 / 2 := by
    have hstep : C0 * ‖ρ⁻¹‖ ≤ C0 * (1 / (2 * (C0 + 1))) := mul_le_mul_of_nonneg_left hi hC0pos
    have : C0 * (1 / (2 * (C0 + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hE3 : d * |(ρ⁻¹).re| ≤ d * ‖ρ⁻¹‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (abs_re_inv_le_norm_sq hρre0 hρre1) hd0.le
  intro x hx
  rw [Set.uIoc_of_le hd0.le] at hx
  have hxabs : |x| ≤ d := by rw [abs_of_nonneg hx.1.le]; exact hx.2
  -- bounds `‖s‖ ≤ C0`, `‖s + d‖ ≤ C0` on the two abscissae
  have hs_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I‖ ≤ C0 := by
    have := Complex.norm_complex_line_le x t; rw [hC0]; linarith
  have hsd_C0 : ‖(1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ)‖ ≤ C0 := by
    have h1 := norm_add_le ((1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I) (d : ℂ)
    have h2 : ‖(d : ℂ)‖ = d := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    have := Complex.norm_complex_line_le x t
    rw [hC0]; rw [h2] at h1; linarith
  -- the two abscissae avoid the zero `ρ` (their ordinate is `t ≠ Im ρ`)
  have h2ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_im x t])
  have h1ne : (1 / 2 : ℂ) + (x : ℂ) + (t : ℂ) * I + (d : ℂ) ≠ ρ := fun h ↦
    ht i (by rw [← hρ, ← h, complex_line_add_im x t d])
  rw [Real.norm_eq_abs, shiftLogIntegrand_eq hρ0 t d x h1ne h2ne]
  refine (abs_sub_sub_le _ _ _).trans ?_
  rw [abs_mul, abs_of_pos hd0]
  refine (add_le_add (add_le_add (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hsd_C0 hsmall)
    (abs_log_norm_one_sub_div_add_re_le (ρ := ρ) hs_C0 hsmall)) hE3).trans (le_of_eq ?_)
  ring

/-- **Summability of the shift-difference integrals** `i ↦ ∫₀ᵈ[log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖]dx`. -/
private lemma summable_shiftLogIntegral {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    Summable (fun i ↦ shiftLogIntegral t d (riemannXiZeros i)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  refine Summable.of_norm_bounded_eventually
    (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
  filter_upwards [hCb] with i hi
  calc ‖shiftLogIntegral t d (riemannXiZeros i)‖
      = ‖∫ x in (0 : ℝ)..d, shiftLogIntegrand t d (riemannXiZeros i) x‖ := by rw [shiftLogIntegral]
    _ ≤ C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 * |d - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hi
    _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by rw [sub_zero, abs_of_pos hd0]; ring

/-- **Sum–integral interchange for the shift integrand** (`lem:ll_booker`). With
`s = 1/2 + x + it`,
`∑ᵢ ∫₀ᵈ[log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] dx = ∫₀ᵈ ∑ᵢ[log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] dx`. -/
theorem tsum_shiftLogIntegral_eq_intervalIntegral_tsum {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
  have hd0 : (0 : ℝ) < d := by linarith
  -- each integrand is integrable on `Ioc 0 d`
  have hint : ∀ i, MeasureTheory.IntegrableOn
      (shiftLogIntegrand t d (riemannXiZeros i)) (Set.Ioc 0 d) := fun i ↦
    (continuous_shiftLogIntegrand t d (ht i)).integrableOn_Ioc
  -- `i ↦ ∫_{Ioc 0 d} ‖shiftLogIntegrand‖` is summable, by the `O(|ρᵢ|⁻²)` bound
  obtain ⟨C, hC0, hCb⟩ := exists_eventually_forall_norm_shiftLogIntegrand_le hd ht
  have hsummint : Summable (fun i ↦
      ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖) := by
    refine Summable.of_norm_bounded_eventually
      (summable_inv_norm_sq_riemannXiZeros.mul_left (C * d)) ?_
    filter_upwards [hCb] with i hi
    have hnn : (0 : ℝ) ≤ ∫ x in Set.Ioc (0 : ℝ) d,
        ‖shiftLogIntegrand t d (riemannXiZeros i) x‖ :=
      MeasureTheory.integral_nonneg (fun x ↦ norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ∫ x in Set.Ioc (0 : ℝ) d, ‖shiftLogIntegrand t d (riemannXiZeros i) x‖
        ≤ ∫ _x in Set.Ioc (0 : ℝ) d, C * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on (hint i).norm ?_ measurableSet_Ioc ?_
          · exact MeasureTheory.integrableOn_const
              (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
          · intro x hx
            exact hi x (by rw [Set.uIoc_of_le hd0.le]; exact hx)
      _ = C * d * ‖(riemannXiZeros i)⁻¹‖ ^ 2 := by
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hd0.le, smul_eq_mul]
          ring
  -- apply the interchange
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun i ↦ shiftLogIntegrand t d (riemannXiZeros i))
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) d)) hint hsummint
  calc ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      = ∑' i, ∫ x in Set.Ioc (0 : ℝ) d, shiftLogIntegrand t d (riemannXiZeros i) x := by
        refine tsum_congr (fun i ↦ ?_)
        rw [shiftLogIntegral, intervalIntegral.integral_of_le hd0.le]
    _ = ∫ x in Set.Ioc (0 : ℝ) d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := hswap
    _ = ∫ x in (0 : ℝ)..d, ∑' i, shiftLogIntegrand t d (riemannXiZeros i) x := by
        rw [intervalIntegral.integral_of_le hd0.le]

/-- **The summed booker bound** (`lem:ll_booker_sum`), parametric in the pairing constant `c ≥ 2`:
`∑ᵢ ∫₀ᵈ[log‖s+d-ρᵢ‖ - log‖s-ρᵢ‖] dx ≤ c d² ∑ᵢ Re 1/(s_d - ρᵢ)`, with `s = 1/2 + x + it` and
`s_d = 1/2 + d + it`. -/
theorem integral_tsum_log_norm_shift_le_of {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) {c : ℝ} (hc : 2 ≤ c) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ c * d ^ 2 * ∑' i,
          (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re := by
  set A : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hA
  set g : ℂ → ℝ := shiftLogIntegral t d with hg
  set f : ℂ → ℝ := fun ρ ↦ ((A - ρ)⁻¹).re with hf
  -- the four summabilities, the reflected ones by the reindexing involution
  have hSg : Summable fun i ↦ g (riemannXiZeros i) := summable_shiftLogIntegral hd ht
  have hSh : Summable fun i ↦ g (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff g).mpr hSg
  have hSc : Summable fun i ↦ f (riemannXiZeros i) := summable_pairDensity hd
  have hSch : Summable fun i ↦ f (1 - starRingEnd ℂ (riemannXiZeros i)) :=
    (summable_riemannXiZeros_one_sub_conj_iff f).mpr hSc
  -- Lehman's per-zero pairing estimate, and the two reflection reindexings
  have hper : ∀ i, g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))
      ≤ c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) := fun i ↦
    shiftLogIntegral_add_le_of t hd (ht i) (riemannXiZeros_re_pos i)
      (riemannXiZeros_re_lt_one i) hc
  have hreflg := tsum_riemannXiZeros_one_sub_conj g
  have hreflc := tsum_riemannXiZeros_one_sub_conj f
  have key : 2 * ∑' i, g (riemannXiZeros i) ≤ 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) :=
    calc 2 * ∑' i, g (riemannXiZeros i)
        = ∑' i, (g (riemannXiZeros i) + g (1 - starRingEnd ℂ (riemannXiZeros i))) := by
          rw [hSg.tsum_add hSh, ← hreflg]; ring
      _ ≤ ∑' i, c * d ^ 2 * (f (riemannXiZeros i) + f (1 - starRingEnd ℂ (riemannXiZeros i))) :=
          Summable.tsum_le_tsum hper (hSg.add hSh) ((hSc.add hSch).mul_left _)
      _ = 2 * (c * d ^ 2 * ∑' i, f (riemannXiZeros i)) := by
          rw [tsum_mul_left, hSc.tsum_add hSch, ← hreflc]; ring
  linarith

/-- The `c = 5/2` case of `integral_tsum_log_norm_shift_le_of`, the constant consumed by the
current lower-bound assembly. -/
theorem integral_tsum_log_norm_shift_le {t d : ℝ} (hd : 1 / 2 < d)
    (ht : ∀ i, (riemannXiZeros i).im ≠ t) :
    ∑' i, shiftLogIntegral t d (riemannXiZeros i)
      ≤ 5 / 2 * d ^ 2 * ∑' i,
          (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re :=
  integral_tsum_log_norm_shift_le_of hd ht (by norm_num)

/-! ## The log-`t` coefficient from the explicit formula (`lem:ll_zeta_sum`) -/

open scoped LSeries.notation
open ArithmeticFunction

/-- **The Dirichlet-series bound on `Re(ζ'/ζ)` for `Re s > 1`**: `Re(ζ'/ζ(s))` is dominated by
`∑ₙ ‖Λ(n) n^{-s}‖`, whose value depends only on `Re s`. -/
lemma re_logDeriv_riemannZeta_le {s : ℂ} (hs : 1 < s.re) :
    (logDeriv riemannZeta s).re ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := by
  have hsum : Summable (fun n ↦ ‖LSeries.term ↗Λ s n‖) := (LSeriesSummable_vonMangoldt hs).norm
  have hlogD : logDeriv riemannZeta s = -LSeries ↗Λ s := by
    rw [logDeriv_apply, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]; ring
  calc (logDeriv riemannZeta s).re
      ≤ ‖logDeriv riemannZeta s‖ := Complex.re_le_norm _
    _ = ‖LSeries ↗Λ s‖ := by rw [hlogD, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum

/-- **Real-part bound on the digamma function.** Given a remainder bound `‖R(z)‖ ≤ C‖z‖⁻¹` at
order `0`, `Re ψ(z) ≤ log‖z‖ + (½+C)/‖z‖` for `Re z > 0`. -/
lemma re_digamma_le {z : ℂ} (hz : 0 < z.re) {C : ℝ}
    (hC : ‖digammaRemainderIoi z 1‖ ≤ C * ‖z‖ ^ (-(1 : ℤ))) :
    (Complex.digamma z).re ≤ Real.log ‖z‖ + (1 / 2 + C) / ‖z‖ := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzne : ‖z‖ ≠ 0 := hznorm.ne'
  have hzpow : ‖z‖ ^ (-(1 : ℤ)) = (‖z‖)⁻¹ := by rw [zpow_neg, zpow_one]
  rw [hzpow] at hC
  have heq := digamma_eq_log_sub z hz 0
  rw [show (2 * 0 + 1) = 1 from rfl,
      show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty_of_lt (by norm_num),
      Finset.sum_empty, sub_zero] at heq
  rw [heq, Complex.sub_re, Complex.sub_re, Complex.log_re]
  have e1 : -((2 * z)⁻¹).re ≤ (2 * ‖z‖)⁻¹ := by
    have hn : ‖(2 * z)⁻¹‖ = (2 * ‖z‖)⁻¹ := by rw [norm_inv, norm_mul, Complex.norm_ofNat]
    calc -((2 * z)⁻¹).re ≤ ‖(2 * z)⁻¹‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ = (2 * ‖z‖)⁻¹ := hn
  have e2 : -(digammaRemainderIoi z 1).re ≤ C * (‖z‖)⁻¹ :=
    le_trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)) hC
  have efr : (2 * ‖z‖)⁻¹ + C * (‖z‖)⁻¹ = (1 / 2 + C) / ‖z‖ := by field_simp
  linarith [e1, e2, efr]

/-- **Bound on the zero sum at the abscissa `s_d = ½ + d + it`** (`lem:ll_zeta_sum`). For `d > ½`
there is a `t`-independent constant `C` with `∑ᵢ Re 1/(s_d - ρᵢ) ≤ ½ log t + C` for `t ≥ 168π`. -/
theorem tsum_re_inv_riemannXiZeros_sub_le {d : ℝ} (hd : 1 / 2 < d) :
    ∃ C : ℝ, ∀ t : ℝ, 168 * π ≤ t →
      ∑' i, (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
        ≤ 1 / 2 * Real.log t + C := by
  refine ⟨(∑' n, ‖LSeries.term ↗Λ ((1 / 2 + d : ℝ) : ℂ) n‖) + 2
      - 1 / 2 * Real.log π + 1 / 2 * ((1 / 2 + d) / (168 * π) + 3 / (1 / 2 + d)), ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hPair := summable_pairDensity (d := d) (t := t) hd
  -- coordinates, side conditions and norm estimates of `s = 1/2 + d + it`
  obtain ⟨hsre, hsim, hre, hreσ, hs1, hsne, hsnorm_lb, -, hsnorm_ub⟩ :=
    shiftedLine_setup hd ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hs_ge1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by linarith) hsnorm_lb
  -- (1) Dirichlet term
  have b1 : (logDeriv riemannZeta s).re ≤ ∑' n, ‖LSeries.term ↗Λ ((1 / 2 + d : ℝ) : ℂ) n‖ :=
    (re_logDeriv_riemannZeta_le hreσ).trans (le_of_eq (tsum_congr fun n ↦ by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre, Complex.ofReal_re]))
  -- (2) polar terms
  have b2 : (1 / s).re ≤ 1 := Complex.one_div_re_le_one hs_ge1
  have hs1_ge1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, hsim, sub_zero, abs_of_pos ht0] at h
    linarith [Real.pi_gt_three]
  have b3 : (1 / (s - 1)).re ≤ 1 := Complex.one_div_re_le_one hs1_ge1
  -- (3) digamma term
  have hz : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hsre]; linarith
  have hdig := re_digamma_le (C := 1) hz
    (by simpa using norm_digammaRemainderIoi_le' (s / 2) hz 1 le_rfl)
  have hnorm_half : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hhalf_lb : (1 / 2 + d) / 2 ≤ ‖s / 2‖ := by rw [hnorm_half]; linarith
  have hfrac_le : (1 / 2 + 1) / ‖s / 2‖ ≤ 3 / (1 / 2 + d) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hhalf_lb (by norm_num : (0 : ℝ) ≤ 3)]
  have hlog_half : Real.log ‖s / 2‖ ≤ Real.log t + (1 / 2 + d) / (168 * π) := by
    have h12 : Real.log ‖s / 2‖ ≤ Real.log (1 / 2 + d + t) := by
      rw [hnorm_half]; exact Real.log_le_log (by linarith) (by linarith)
    have h3 := Real.log_add_le (u := 1 / 2 + d) (t := t) (by linarith) ht0
    have h4 : (1 / 2 + d) / t ≤ (1 / 2 + d) / (168 * π) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) ht
    linarith
  -- solve the explicit formula for the zero sum and bound each right-hand term
  rw [tsum_re_inv_riemannXiZeros_sub_eq hre hs1 hsne hPair]
  linarith [b1, b2, b3, hdig, hlog_half, hfrac_le]

