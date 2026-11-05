/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous argument variation along a path

For a continuous nowhere-zero `φ : ℝ → ℂ`, a *continuous logarithm* of `φ` on `[a, b]` is a
`g : ℝ → ℂ`, continuous on `[a, b]`, with `exp (g u) = φ u` there; the *argument variation* of
`φ` is `Im (g b) - Im (g a)`, independent of the choice of `g`.

## Main definitions

- `IsContLog`: the predicate "`g` is a continuous logarithm of `φ` on `[a, b]`".
- `argVariation`: the argument variation `Δ arg φ` (junk value `0` when no continuous logarithm
  exists).
- `lineSeg`: the affine segment `z₀ → z₁` parametrised over `[0, 1]`, the path primitive along
  which argument variation is computed.

## Main results

- `exists_isContLog`, `exists_isContLog_of_ne_zero`: existence of a continuous logarithm, with or
  without a prescribed left value.
- `IsContLog.sub_const`, `IsContLog.im_sub_eq`: uniqueness up to an additive constant, and
  well-definedness of the variation.
- `argVariation_mul`, `argVariation_trans`, `argVariation_reverse`, `argVariation_comp`:
  multiplicativity, concatenation additivity, reversal, reparametrisation invariance.
- `argVariation_eq_arg_sub_arg`: slit-plane evaluation.
- `argVariation_eq_im_integral`: the logarithmic-derivative integral formula.
-/
@[expose] public section


open scoped Topology

variable {a b : ℝ}

/-- `g : ℝ → ℂ` is a *continuous logarithm* of `φ` on `[a, b]` if it is continuous on
`[a, b]` and `exp (g u) = φ u` there. -/
def IsContLog (a b : ℝ) (φ g : ℝ → ℂ) : Prop :=
  ContinuousOn g (Set.Icc a b) ∧ ∀ u ∈ Set.Icc a b, Complex.exp (g u) = φ u

namespace IsContLog

/-- `φ` is automatically continuous on `[a, b]` if it has a continuous logarithm there. -/
theorem continuousOn {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) :
    ContinuousOn φ (Set.Icc a b) :=
  (Complex.continuous_exp.comp_continuousOn hg.1).congr fun u hu => (hg.2 u hu).symm

/-- `φ` is automatically nowhere zero on `[a, b]` if it has a continuous logarithm there. -/
theorem ne_zero {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) {u : ℝ} (hu : u ∈ Set.Icc a b) :
    φ u ≠ 0 := by
  rw [← hg.2 u hu]; exact Complex.exp_ne_zero _

end IsContLog

/-- The subtype `↥(Set.Icc a b)` is simply connected when `a ≤ b`. This cannot be a global
instance: for `b < a` the subtype is empty, hence not simply connected. -/
theorem simplyConnectedSpace_Icc (hab : a ≤ b) :
    SimplyConnectedSpace ↥(Set.Icc a b) := by
  have : ContractibleSpace ↥(Set.Icc a b) :=
    (convex_Icc a b).contractibleSpace ⟨a, Set.left_mem_Icc.mpr hab⟩
  infer_instance

/-- The subtype `↥(Set.Icc a b)` is locally path connected. -/
instance instLocallyPathConnectedSpaceIcc :
    LocallyPathConnectedSpace ↥(Set.Icc a b) :=
  (convex_Icc a b).locallyPathConnectedSpace

/-- **Existence of a continuous logarithm** with prescribed value at the left endpoint.
If `φ` is continuous and nowhere zero on `[a, b]` and `exp c = φ a`, then there is a
continuous logarithm `g` of `φ` on `[a, b]` with `g a = c`. -/
theorem exists_isContLog (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    {c : ℂ} (hc : Complex.exp c = φ a) :
    ∃ g : ℝ → ℂ, IsContLog a b φ g ∧ g a = c := by
  have := simplyConnectedSpace_Icc hab
  -- The bundled restriction of `φ` to the interval subtype.
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, hφ.domRestrict⟩
  have hs : ∀ x : ↥(Set.Icc a b), f x ∈ ({0}ᶜ : Set ℂ) := fun x =>
    Set.mem_compl_singleton_iff.mpr (h0 x.1 x.2)
  have he : Complex.exp c = f ⟨a, Set.left_mem_Icc.mpr hab⟩ := hc
  obtain ⟨F, ⟨hFa, hFp⟩, -⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  refine ⟨fun u => F (Set.projIcc a b hab u), ⟨?_, ?_⟩, ?_⟩
  · exact (F.continuous.comp continuous_projIcc).continuousOn
  · intro u hu
    change Complex.exp (F (Set.projIcc a b hab u)) = φ u
    have hcong := congrFun hFp (Set.projIcc a b hab u)
    simp only [Function.comp_apply] at hcong
    rw [hcong, Set.projIcc_of_mem hab hu]
    rfl
  · change F (Set.projIcc a b hab a) = c
    rw [Set.projIcc_of_mem hab (Set.left_mem_Icc.mpr hab)]
    exact hFa

/-- **Existence of a continuous logarithm** for a continuous nowhere-zero `φ` on `[a, b]`,
with no constraint on the endpoint value. -/
theorem exists_isContLog_of_ne_zero (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    ∃ g, IsContLog a b φ g :=
  let ⟨g, hg, _⟩ := exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  ⟨g, hg⟩

/-- **Uniqueness up to an additive constant.** Two continuous logarithms of the same `φ`
on `[a, b]` differ by the constant `g₁ a - g₂ a`. -/
theorem IsContLog.sub_const (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    ∀ u ∈ Set.Icc a b, g₁ u - g₂ u = g₁ a - g₂ a := by
  have := simplyConnectedSpace_Icc hab
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  set k : ℂ := g₁ a - g₂ a with hk
  -- the restricted continuous logarithms as bundled maps
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, h1.continuousOn.domRestrict⟩
  let F₁ : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict g₁, h1.1.domRestrict⟩
  let F₂ : C(↥(Set.Icc a b), ℂ) :=
    ⟨fun x => (Set.Icc a b).domRestrict g₂ x + k, (h2.1.domRestrict).add continuous_const⟩
  have hexpk : Complex.exp k = 1 := by
    rw [hk, Complex.exp_sub, h1.2 a hamem, h2.2 a hamem, div_self (h1.ne_zero hamem)]
  have hP1 : F₁ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₁ = ⇑f := by
    refine ⟨rfl, funext fun x => ?_⟩
    simpa [F₁, f] using h1.2 x.1 x.2
  have hP2 : F₂ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₂ = ⇑f := by
    refine ⟨by simp only [F₂, ContinuousMap.coe_mk, Set.domRestrict_apply, hk]; ring,
      funext fun x => ?_⟩
    simp only [F₂, f, Function.comp_apply, ContinuousMap.coe_mk, Set.domRestrict_apply,
      Complex.exp_add, hexpk, mul_one]
    exact h2.2 x.1 x.2
  have huniq := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (e₀ := g₁ a) (a₀ := ⟨a, hamem⟩) (h1.2 a hamem)
    (fun x => Set.mem_compl_singleton_iff.mpr (h1.ne_zero x.2))
  have hF : F₁ = F₂ := huniq.unique hP1 hP2
  intro u hu
  have := DFunLike.congr_fun hF ⟨u, hu⟩
  simp only [F₁, F₂, ContinuousMap.coe_mk, Set.domRestrict_apply] at this
  rw [this]; ring

/-- **Well-definedness of the argument variation.** The quantity `Im (g b) - Im (g a)`
does not depend on the choice of continuous logarithm `g`. -/
theorem IsContLog.im_sub_eq (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    (g₁ b).im - (g₁ a).im = (g₂ b).im - (g₂ a).im := by
  have key := h1.sub_const hab h2 b (Set.right_mem_Icc.mpr hab)
  have hsub : (g₁ b - g₂ b).im = (g₁ a - g₂ a).im := by rw [key]
  simp only [Complex.sub_im] at hsub
  linarith

open Classical in
/-- The **argument variation** `Δ arg φ = Im (g b) - Im (g a)` of `φ` over `[a, b]`, for any
continuous logarithm `g` of `φ`. Junk value `0` when no continuous logarithm exists. -/
noncomputable def argVariation (a b : ℝ) (φ : ℝ → ℂ) : ℝ :=
  if h : ∃ g, IsContLog a b φ g then (h.choose b).im - (h.choose a).im else 0

/-- The argument variation computed from any continuous logarithm. -/
theorem argVariation_eq_of_isContLog (hab : a ≤ b) {φ g : ℝ → ℂ}
    (hg : IsContLog a b φ g) : argVariation a b φ = (g b).im - (g a).im := by
  have hex : ∃ g, IsContLog a b φ g := ⟨g, hg⟩
  rw [argVariation, dif_pos hex]
  exact IsContLog.im_sub_eq hab hex.choose_spec hg

/-- **Congruence.** If `φ` and `ψ` agree on `[a, b]`, their argument variations agree. -/
theorem argVariation_congr (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (h : Set.EqOn φ ψ (Set.Icc a b)) : argVariation a b φ = argVariation a b ψ := by
  by_cases hex : ∃ g, IsContLog a b φ g
  · obtain ⟨g, hg⟩ := hex
    have hg' : IsContLog a b ψ g := ⟨hg.1, fun u hu => (hg.2 u hu).trans (h hu)⟩
    rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog hab hg']
  · have hex' : ¬ ∃ g, IsContLog a b ψ g := fun ⟨g, hg⟩ =>
      hex ⟨g, hg.1, fun u hu => (hg.2 u hu).trans (h hu).symm⟩
    unfold argVariation
    rw [dif_neg hex, dif_neg hex']

/-- **Multiplicativity in the integrand.** -/
theorem argVariation_mul (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0φ : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hψ : ContinuousOn ψ (Set.Icc a b)) (h0ψ : ∀ u ∈ Set.Icc a b, ψ u ≠ 0) :
    argVariation a b (φ * ψ) = argVariation a b φ + argVariation a b ψ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0φ
  obtain ⟨h, hh⟩ := exists_isContLog_of_ne_zero hab hψ h0ψ
  have hgh : IsContLog a b (φ * ψ) (g + h) := by
    refine ⟨hg.1.add hh.1, fun u hu => ?_⟩
    simp only [Pi.add_apply, Complex.exp_add, hg.2 u hu, hh.2 u hu, Pi.mul_apply]
  rw [argVariation_eq_of_isContLog hab hgh, argVariation_eq_of_isContLog hab hg,
    argVariation_eq_of_isContLog hab hh]
  simp only [Pi.add_apply, Complex.add_im]
  ring

/-- **Additivity under concatenation.** -/
theorem argVariation_trans {m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b φ = argVariation a m φ + argVariation m b φ := by
  have hab : a ≤ b := ham.trans hmb
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hsub_am : Set.Icc a m ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hmb
  have hsub_mb : Set.Icc m b ⊆ Set.Icc a b := Set.Icc_subset_Icc ham le_rfl
  have hg_am : IsContLog a m φ g := ⟨hg.1.mono hsub_am, fun u hu => hg.2 u (hsub_am hu)⟩
  have hg_mb : IsContLog m b φ g := ⟨hg.1.mono hsub_mb, fun u hu => hg.2 u (hsub_mb hu)⟩
  rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog ham hg_am,
    argVariation_eq_of_isContLog hmb hg_mb]
  ring

/-- **Reversal.** Traversing `[a, b]` backwards negates the argument variation. -/
theorem argVariation_reverse (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => φ (a + b - u)) = - argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hmap : Set.MapsTo (fun u : ℝ => a + b - u) (Set.Icc a b) (Set.Icc a b) := by
    intro u hu
    simp only [Set.mem_Icc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hcont : Continuous (fun u : ℝ => a + b - u) := by fun_prop
  have hg' : IsContLog a b (fun u => φ (a + b - u)) (fun u => g (a + b - u)) := by
    refine ⟨hg.1.comp hcont.continuousOn hmap, fun u hu => hg.2 (a + b - u) (hmap hu)⟩
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  rw [show a + b - b = a by ring, show a + b - a = b by ring]
  ring

/-- **Invariance under endpoint-preserving reparametrisation.** For `σ : [a', b'] → [a, b]`
continuous with `σ a' = a` and `σ b' = b`, and `φ` continuous and nowhere zero on `[a, b]`,
`argVariation a' b' (fun v => φ (σ v)) = argVariation a b φ`. -/
theorem argVariation_comp {a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    {σ : ℝ → ℝ} (hσc : ContinuousOn σ (Set.Icc a' b'))
    (hσmap : Set.MapsTo σ (Set.Icc a' b') (Set.Icc a b))
    (hσa : σ a' = a) (hσb : σ b' = b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a' b' (fun v => φ (σ v)) = argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hg' : IsContLog a' b' (fun v => φ (σ v)) (fun v => g (σ v)) :=
    ⟨hg.1.comp hσc hσmap, fun v hv => hg.2 (σ v) (hσmap hv)⟩
  rw [argVariation_eq_of_isContLog hab' hg', argVariation_eq_of_isContLog hab hg, hσa, hσb]

/-- **Slit-plane evaluation.** If the path stays in the slit plane, the argument variation
is the difference of principal arguments. -/
theorem argVariation_eq_arg_sub_arg (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (hsp : ∀ u ∈ Set.Icc a b, φ u ∈ Complex.slitPlane) :
    argVariation a b φ = (φ b).arg - (φ a).arg := by
  have hlog : IsContLog a b φ (fun u => Complex.log (φ u)) :=
    ⟨hφ.clog hsp, fun u hu => Complex.exp_log (Complex.slitPlane_ne_zero (hsp u hu))⟩
  rw [argVariation_eq_of_isContLog hab hlog, Complex.log_im, Complex.log_im]

/-- `Complex.exp` is injective on any ball of radius `π`. -/
private theorem injOn_exp_ball (z₀ : ℂ) :
    Set.InjOn Complex.exp (Metric.ball z₀ Real.pi) := by
  intro z hz w hw hzw
  have h1 : Complex.exp (z - w) = 1 := by
    rw [Complex.exp_sub, hzw, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hd : ‖z - w‖ < 2 * Real.pi := by
    calc ‖z - w‖ = ‖(z - z₀) - (w - z₀)‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖w - z₀‖ := norm_sub_le _ _
      _ < Real.pi + Real.pi := by
          rw [mem_ball_iff_norm] at hz hw; exact add_lt_add hz hw
      _ = 2 * Real.pi := by ring
  have him : (z - w).im = 2 * Real.pi * n := by
    rw [hn]; simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]; ring
  have hbound : |2 * Real.pi * (n : ℝ)| ≤ ‖z - w‖ := him ▸ Complex.abs_im_le_norm _
  have hn0 : n = 0 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
    have : |n| < 1 := by exact_mod_cast (by nlinarith [Real.pi_pos] : |(n : ℝ)| < 1)
    have := abs_lt.mp this; omega
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  exact sub_eq_zero.mp hn

/-- **A continuous logarithm is a primitive of `φ'/φ`.** If `φ` is differentiable at an
interior point `u₀` of `[a, b]` with derivative `φ'`, then any continuous logarithm `g` of
`φ` is differentiable there with `g'(u₀) = φ'/φ(u₀)`. -/
theorem IsContLog.hasDerivAt {φ g : ℝ → ℂ} (hg : IsContLog a b φ g)
    {u₀ : ℝ} (hu₀ : u₀ ∈ Set.Ioo a b) {φ' : ℂ} (hφ' : HasDerivAt φ φ' u₀) :
    HasDerivAt g (φ' / φ u₀) u₀ := by
  have hu₀I : u₀ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hu₀
  have hw₀ : φ u₀ ≠ 0 := hg.ne_zero hu₀I
  -- choose a rotation `r ∈ {1, -1}` bringing `φ u₀` into the slit plane
  obtain ⟨r, hr0, hrsp⟩ : ∃ r : ℂ, r ≠ 0 ∧ r * φ u₀ ∈ Complex.slitPlane := by
    rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hw₀ with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  -- the explicit slit-plane branch `L` and its derivative
  set L : ℝ → ℂ := fun u => Complex.log (r * φ u) - Complex.log r with hL_def
  have hL : HasDerivAt L (φ' / φ u₀) u₀ := by
    have h3 := ((Complex.hasDerivAt_log hrsp).comp u₀ (hφ'.const_mul r)).sub_const (Complex.log r)
    rw [inv_mul_eq_div, mul_div_mul_left _ _ hr0] at h3
    exact h3
  -- `L` exponentiates to `φ` wherever `r * φ` stays in the slit plane
  have hLexp : ∀ u, r * φ u ∈ Complex.slitPlane → Complex.exp (L u) = φ u := by
    intro u hu
    rw [hL_def, Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero hu),
      Complex.exp_log hr0, mul_comm, mul_div_assoc, div_self hr0, mul_one]
  -- neighbourhoods: `r * φ` stays in the slit plane, and `Icc a b` is a neighbourhood of `u₀`
  have hφc : ContinuousAt φ u₀ := hφ'.continuousAt
  have hIccnhds : Set.Icc a b ∈ 𝓝 u₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu₀) Set.Ioo_subset_Icc_self
  have hgc : ContinuousAt g u₀ := hg.1.continuousAt hIccnhds
  have hsp_nhds : ∀ᶠ u in 𝓝 u₀, r * φ u ∈ Complex.slitPlane :=
    (hφc.const_mul r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hrsp)
  -- both `g` and `L + k₀` exponentiate to `φ` and tend to `g u₀`, so they agree near `u₀`
  set k₀ : ℂ := g u₀ - L u₀ with hk₀
  have hLkval : L u₀ + k₀ = g u₀ := by rw [hk₀]; ring
  have hLkc : ContinuousAt (fun u => L u + k₀) u₀ := hL.continuousAt.add continuousAt_const
  have hg_ball : ∀ᶠ u in 𝓝 u₀, g u ∈ Metric.ball (g u₀) Real.pi :=
    hgc.eventually_mem (Metric.ball_mem_nhds _ Real.pi_pos)
  have hLk_ball : ∀ᶠ u in 𝓝 u₀, (fun u => L u + k₀) u ∈ Metric.ball (g u₀) Real.pi := by
    apply hLkc.eventually_mem
    apply Metric.isOpen_ball.mem_nhds
    show L u₀ + k₀ ∈ Metric.ball (g u₀) Real.pi
    rw [hLkval]; exact Metric.mem_ball_self Real.pi_pos
  have hg_exp : ∀ᶠ u in 𝓝 u₀, Complex.exp (g u) = φ u := by
    filter_upwards [hIccnhds] with u hu using hg.2 u hu
  have hexpk : Complex.exp k₀ = 1 := by
    rw [hk₀, Complex.exp_sub, hg.2 u₀ hu₀I, hLexp u₀ hrsp, div_self hw₀]
  have hev : g =ᶠ[𝓝 u₀] (fun u => L u + k₀) := by
    filter_upwards [hg_ball, hLk_ball, hg_exp, hsp_nhds] with u hu1 hu2 hu3 hu4
    apply injOn_exp_ball (g u₀) hu1 hu2
    rw [hu3]
    simp only [Complex.exp_add, hLexp u hu4, hexpk, mul_one]
  exact (hL.add_const k₀).congr_of_eventuallyEq hev

/-- **Logarithmic-derivative integral formula.** If `φ` is nowhere zero and continuously
differentiable on `[a, b]` with derivative `φ'`, then the argument variation is the
imaginary part of the integral of the logarithmic derivative `φ'/φ`. -/
theorem argVariation_eq_im_integral (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u => φ' u / φ u) (Set.Icc a b)) :
    argVariation a b φ = (∫ u in a..b, φ' u / φ u).im := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hgderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt g (φ' u / φ u) u :=
    fun u hu => hg.hasDerivAt hu (hderiv u hu)
  have hftc : ∫ u in a..b, φ' u / φ u = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
      (fun u hu => (hgderiv u hu).hasDerivWithinAt) (hint.intervalIntegrable_of_Icc hab)
  rw [argVariation_eq_of_isContLog hab hg, hftc, Complex.sub_im]

/-- The affine segment from `z₀` to `z₁`, parametrised over `[0, 1]`. -/
noncomputable def lineSeg (z₀ z₁ : ℂ) (u : ℝ) : ℂ := z₀ + (u : ℂ) * (z₁ - z₀)

/-- The segment starts at `z₀`. -/
@[simp] theorem lineSeg_zero (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 0 = z₀ := by simp [lineSeg]

/-- The segment ends at `z₁`. -/
@[simp] theorem lineSeg_one (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 1 = z₁ := by
  simp only [lineSeg, Complex.ofReal_one, one_mul]; ring

/-- The real part along the segment. -/
theorem lineSeg_re (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).re = z₀.re + u * (z₁.re - z₀.re) := by
  simp [lineSeg, Complex.add_re, Complex.mul_re, Complex.sub_re]

/-- The imaginary part along the segment. -/
theorem lineSeg_im (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).im = z₀.im + u * (z₁.im - z₀.im) := by
  simp [lineSeg, Complex.add_im, Complex.mul_im, Complex.sub_im]

/-- The segment is continuous in its parameter. -/
theorem continuous_lineSeg (z₀ z₁ : ℂ) : Continuous (lineSeg z₀ z₁) := by
  unfold lineSeg; fun_prop

/-- Subtracting a constant `c` from the segment shifts both endpoints by `c`. -/
theorem lineSeg_sub_const (z₀ z₁ c : ℂ) :
    (fun u => lineSeg z₀ z₁ u - c) = lineSeg (z₀ - c) (z₁ - c) := by
  funext u; simp only [lineSeg]; ring

