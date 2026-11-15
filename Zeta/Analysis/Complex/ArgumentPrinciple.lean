/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Order.Interval.Set.Infinite
public import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
public import Zeta.Analysis.Complex.ArgVariation

/-!
# The argument principle on a rectangle

The argument principle for an analytic `f` on a closed rectangle: the number of zeros inside,
counted with multiplicity, is `(1/2π) · Δ_{∂R} arg f`. Along the way, the residue of the
logarithmic derivative at a zero of order `n` is `n`.

## Main definitions

- `rectangleArgVariation`: the counterclockwise boundary argument variation `Δ_{∂R} arg f`, the
  sum over the four oriented edges of the rectangle.

## Main results

- `meromorphicOrderAt_eq_residue_logDeriv`: the decomposition of `logDeriv f` into its singular
  part `n / (z - z₀)` and a holomorphic remainder.
- `finite_rectangle_inter_setOf_eq_zero`: an analytic function has finitely many zeros in a
  closed rectangle.
- `rectangleIntegral_logDeriv_eq_two_pi_I_sum`: `RectangleIntegral (logDeriv f) z w`
  `= 2πi · ∑_ρ mult ρ`, with `rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton` its
  single-zero case.
- `rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation`: that boundary integral equals
  `I · Δ_{∂R} arg f`.
- `rectangle_zero_count_eq_argVariation`: the **argument principle**,
  `∑_ρ mult ρ = (1 / 2π) · Δ_{∂R} arg f`.
- `rectangleArgVariation_eq_zero_of_analyticOnNhd`: `Δ_{∂R} arg f = 0` for non-vanishing `f`.
-/
@[expose] public section


open Complex Filter Topology Asymptotics

/-- The logarithmic derivative of an analytic function is analytic wherever the function does
not vanish. -/
private theorem analyticAt_logDeriv {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) :
    AnalyticAt ℂ (logDeriv f) x :=
  show AnalyticAt ℂ (fun z ↦ deriv f z / f z) x from hf.deriv.div hf h0

/-- The logarithmic derivative of a function analytic on `U` is holomorphic on any subset of `U`
on which the function does not vanish. -/
private theorem holomorphicOn_logDeriv {f : ℂ → ℂ} {U S : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hSU : S ⊆ U) (h0 : ∀ x ∈ S, f x ≠ 0) : HolomorphicOn (logDeriv f) S := fun x hx ↦
  (analyticAt_logDeriv (hf x (hSU hx)) (h0 x hx)).differentiableAt.differentiableWithinAt

/-- For `f` analytic at `z₀` and not eventually zero,
of order `n`, there is an analytic `g` with `g(z₀) ≠ 0` such that
`logDeriv f z = n / (z - z₀) + logDeriv g z` on a punctured neighbourhood of `z₀`, with
`logDeriv g` analytic at `z₀`: the logarithmic derivative has a simple pole of residue `n`. -/
theorem meromorphicOrderAt_eq_residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hf0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      meromorphicOrderAt f z₀ = (n : ℤ) ∧
      AnalyticAt ℂ (logDeriv g) z₀ ∧
      logDeriv f =ᶠ[𝓝[≠] z₀] fun z ↦ (n : ℂ) / (z - z₀) + logDeriv g z := by
  obtain ⟨n, g, hg_an, hg_ne, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hf0
  have hord : meromorphicOrderAt f z₀ = (n : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_natCast.mpr ⟨g, hg_an, hg_ne, hfg⟩]; rfl
  refine ⟨n, g, hg_an, hg_ne, hord, analyticAt_logDeriv hg_an hg_ne, ?_⟩
  have hfg' : f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ n • g z := hfg
  -- `logDeriv f =ᶠ logDeriv (fun z ↦ (z - z₀)^n • g z)` on a full neighbourhood
  refine ((hfg'.deriv.div hfg').filter_mono nhdsWithin_le_nhds).trans ?_
  -- evaluate the right-hand side off `z₀`
  filter_upwards [self_mem_nhdsWithin,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz hgz hgan
  have hpow : (z - z₀) ^ n ≠ 0 :=
    pow_ne_zero n (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz))
  -- rewrite the smul as a product, then split off the polynomial factor's `n / (z - z₀)`
  have key : deriv (fun w ↦ (w - z₀) ^ n • g w) z / ((z - z₀) ^ n • g z)
      = logDeriv (fun w ↦ (w - z₀) ^ n * g w) z := by simp only [smul_eq_mul, logDeriv_apply]
  have hpow_log := logDeriv_fun_pow (f := fun w : ℂ ↦ w - z₀) (x := z) (by fun_prop) n
  simp only [Pi.div_apply]
  rw [key, logDeriv_fun_mul z hpow hgz (by fun_prop) hgan.differentiableAt, hpow_log,
    logDeriv_apply]
  simp [div_eq_mul_inv]

/-- For `f` analytic on a connected `U` and not identically
zero (witnessed by `z₀ ∈ U` with `f z₀ ≠ 0`), and `Rectangle z w ⊆ U`, the zero set
`Rectangle z w ∩ {ρ | f ρ = 0}` is finite. -/
theorem finite_rectangle_inter_setOf_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hsub : Rectangle z w ⊆ U)
    (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    (Rectangle z w ∩ {ρ | f ρ = 0}).Finite := by
  have hcompact : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  refine IsCompact.finite ?_ ?_
  · -- `{z | f z = 0}` is relatively closed on the rectangle, so the intersection is compact
    exact hcompact.of_isClosed_subset ((hf.continuousOn.mono hsub).preimage_isClosed_of_isClosed
      (t := {0}) hcompact.isClosed isClosed_singleton) Set.inter_subset_left
  · -- the intersection is discrete, being a subset of the codiscrete zero set in `U`
    rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hz₀ hz₀U hU))
      (Set.inter_subset_inter_right _ hsub)

/-- A point of `Rectangle z w` not on its boundary has the rectangle as a neighbourhood. -/
theorem rectangle_mem_nhds_of_not_mem_rectangleBorder {z w ρ : ℂ}
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hρRect : ρ ∈ Rectangle z w) (hρ : ρ ∉ RectangleBorder z w) :
    Rectangle z w ∈ 𝓝 ρ := by
  rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hzw_re,
    Set.uIoo_of_le hzw_im, Set.mem_Ioo, Set.mem_Ioo]
  obtain ⟨hr1, hr2, hi1, hi2⟩ := (mem_Rect hzw_re hzw_im ρ).mp hρRect
  have hreIcc : ρ.re ∈ Set.uIcc z.re w.re := by rw [Set.uIcc_of_le hzw_re]; exact ⟨hr1, hr2⟩
  have himIcc : ρ.im ∈ Set.uIcc z.im w.im := by rw [Set.uIcc_of_le hzw_im]; exact ⟨hi1, hi2⟩
  -- each strict inequality can only fail on an edge of `RectangleBorder z w`, contradicting `hρ`;
  -- the disjuncts follow the four edges in the (left-associated) union defining `RectangleBorder`
  refine ⟨⟨hr1.lt_of_ne ?_, hr2.lt_of_ne ?_⟩, hi1.lt_of_ne ?_, hi2.lt_of_ne ?_⟩
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨h.symm, himIcc⟩))))
  · exact fun h ↦ hρ (Or.inr (Complex.mem_reProdIm.mpr ⟨h, himIcc⟩))
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr ⟨hreIcc, h.symm⟩))))
  · exact fun h ↦ hρ (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨hreIcc, h⟩)))

/-- The single-zero case of the rectangle residue formula for `logDeriv f`. For `f` analytic on
a set containing the positively oriented `Rectangle z w`, non-vanishing on its boundary and
with at most one zero inside,
`RectangleIntegral (logDeriv f) z w = 2πi · ∑_{ρ ∈ Z} (meromorphicOrderAt f ρ).untopD 0`,
`Z = Rectangle z w ∩ {ρ | f ρ = 0}`. The finiteness witness `hfin`, though implied by `hss`, is a
hypothesis so that the conclusion is indexed by `hfin.toFinset` as in the general case. -/
theorem rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hss : (Rectangle z w ∩ {ρ | f ρ = 0}).Subsingleton) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  rcases hss.eq_empty_or_singleton with hZ | ⟨ρ, hZ⟩
  · -- No zeros in the rectangle: the integral and the (empty) sum both vanish.
    rw [Set.Finite.toFinset_eq_empty.mpr hZ, Finset.sum_empty, mul_zero]
    exact (holomorphicOn_logDeriv hf hsub fun x hx h0 ↦ Set.notMem_empty x
      (hZ ▸ (⟨hx, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))).vanishesOnRectangle (subset_refl _)
  · -- A single zero `ρ` in the rectangle; it lies in the interior.
    have hρZ : ρ ∈ Rectangle z w ∩ {ρ | f ρ = 0} := hZ ▸ Set.mem_singleton ρ
    have hρnhds : Rectangle z w ∈ 𝓝 ρ :=
      rectangle_mem_nhds_of_not_mem_rectangleBorder hzw_re hzw_im hρZ.1 fun h ↦ hbd ρ h hρZ.2
    -- away from `ρ`, `f` does not vanish on the rectangle, so `logDeriv f` is holomorphic there
    have hfne : ∀ x ∈ Rectangle z w \ {ρ}, f x ≠ 0 := fun x hx h0 ↦
      hx.2 (hZ ▸ (⟨hx.1, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))
    -- `f` is not eventually zero at `ρ`, so the residue decomposition applies
    have hne : ¬ ∀ᶠ x in 𝓝 ρ, f x = 0 := fun hev ↦ by
      have h2 : ∀ᶠ x in 𝓝[≠] ρ, f x ≠ 0 := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hρnhds, self_mem_nhdsWithin] with x hx hx'
          using hfne x ⟨hx, hx'⟩
      obtain ⟨x, hx0, hxne⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and h2).exists
      exact hxne hx0
    obtain ⟨n, g, -, -, hord, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv (hf ρ (hsub hρZ.1)) hne
    -- `logDeriv f - n/(· - ρ)` is `O(1)` near `ρ`, as it agrees with the analytic `logDeriv g`
    have near_p : (logDeriv f - fun s ↦ (n : ℂ) / (s - ρ)) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [heq] with x hx; simp only [Pi.sub_apply]; rw [hx]; ring)
        ((Filter.Tendsto.isBigO_one ℂ hlogg.continuousAt).mono nhdsWithin_le_nhds)
    have hres : RectangleIntegral' (logDeriv f) z w = (n : ℂ) :=
      ResidueTheoremOnRectangleWithSimplePole' hzw_re hzw_im hρnhds
        (holomorphicOn_logDeriv hf (Set.sdiff_subset.trans hsub) hfne) near_p
    -- convert `RectangleIntegral'` back to `RectangleIntegral` (factor `2πi`) and sum over `{ρ}`
    have htf : hfin.toFinset = {ρ} := by ext x; simp [hZ]
    rw [RectangleIntegral', smul_eq_mul] at hres
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero] at hres
    rw [htf, Finset.sum_singleton, hord, WithTop.untopD_coe]
    push_cast; linear_combination hres

/-- A real number strictly between two distinct reals and avoiding a given finite set. -/
private theorem exists_mem_Ioo_not_mem_finset {S : Finset ℝ} {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) :
    ∃ a : ℝ, min r₁ r₂ < a ∧ a < max r₁ r₂ ∧ a ∉ S := by
  obtain ⟨a, ha, haS⟩ :=
    ((Set.Ioo_infinite (min_lt_max.mpr h)).sdiff S.finite_toSet).nonempty
  exact ⟨a, ha.1, ha.2, by simpa using haS⟩

/-- The real part of a rectangle corner `x + y·i`. -/
private theorem ofReal_add_mul_I_re (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp

/-- The imaginary part of a rectangle corner `x + y·i`. -/
private theorem ofReal_add_mul_I_im (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

/-- Every boundary point of either half of a vertical cut at `re = a` (the left half
`Rectangle z (a + w.im·i)` and the right half `Rectangle (a + z.im·i) w`) lies on the cut line
`re = a` or on the boundary of the full rectangle. -/
private theorem rectangleBorder_vcut {z w : ℂ} {a : ℝ} (hza : z.re ≤ a) (haw : a ≤ w.re) :
    RectangleBorder z (↑a + ↑w.im * I) ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w ∧
      RectangleBorder (↑a + ↑z.im * I) w ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w := by
  have ha : a ∈ Set.uIcc z.re w.re := Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.re ∈ Set.uIcc z.re a → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ha ·) <;>
    have h₂ : ρ.re ∈ Set.uIcc a w.re → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc ha Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto

/-- Every boundary point of either half of a horizontal cut at `im = b` (the bottom half
`Rectangle z (w.re + b·i)` and the top half `Rectangle (z.re + b·i) w`) lies on the cut line
`im = b` or on the boundary of the full rectangle. -/
private theorem rectangleBorder_hcut {z w : ℂ} {b : ℝ} (hzb : z.im ≤ b) (hbw : b ≤ w.im) :
    RectangleBorder z (↑w.re + ↑b * I) ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w ∧
      RectangleBorder (↑z.re + ↑b * I) w ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w := by
  have hb : b ∈ Set.uIcc z.im w.im := Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.im ∈ Set.uIcc z.im b → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc hb ·) <;>
    have h₂ : ρ.im ∈ Set.uIcc b w.im → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc hb Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto

/-- Zero-set bookkeeping for a subdivision half: if membership of a zero in the sub-rectangle
`Rectangle P Q ⊆ Rectangle z w` is characterised by a predicate `p`, then the sub-rectangle's
zero set is the `p`-filtered part of the full one. -/
private theorem toFinset_sub_eq_filter {f : ℂ → ℂ} {z w P Q : ℂ}
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hfinP : (Rectangle P Q ∩ {ρ | f ρ = 0}).Finite)
    (hPQ : Rectangle P Q ⊆ Rectangle z w) (p : ℂ → Prop) [DecidablePred p]
    (h : ∀ ρ ∈ Rectangle z w, f ρ = 0 → (ρ ∈ Rectangle P Q ↔ p ρ)) :
    hfinP.toFinset = hfin.toFinset.filter p := by
  ext ρ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hρP, hf0⟩ ↦ ⟨⟨hPQ hρP, hf0⟩, (h ρ (hPQ hρP) hf0).mp hρP⟩,
    fun ⟨⟨hρR, hf0⟩, hp⟩ ↦ ⟨(h ρ hρR hf0).mpr hp, hf0⟩⟩

/-- One subdivision step of the residue-sum induction, splitting `Rectangle z w` along the line
`c = a` (`c` a real coordinate, `Complex.re` or `Complex.im`) between two zeros `ρ₁, ρ₂`. It is
shared by the vertical and horizontal cuts; the caller supplies only the geometry that differs
between the two orientations. -/
private theorem rectangleIntegral_logDeriv_subdivide {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    {N : ℕ} {z w Q₁ P₂ ρ₁ ρ₂ : ℂ} {c : ℂ → ℝ} {a : ℝ}
    (ih : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
    (hsub : Rectangle z w ⊆ U) (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hcard : hfin.toFinset.card ≤ N + 1)
    (hρ₁ : ρ₁ ∈ hfin.toFinset) (hρ₂ : ρ₂ ∈ hfin.toFinset)
    (ha1 : min (c ρ₁) (c ρ₂) < a) (ha2 : a < max (c ρ₁) (c ρ₂))
    (hane : ∀ ρ ∈ hfin.toFinset, c ρ ≠ a)
    (hsubR₁R : Rectangle z Q₁ ⊆ Rectangle z w) (hsubR₂R : Rectangle P₂ w ⊆ Rectangle z w)
    (hre1 : z.re ≤ Q₁.re) (him1 : z.im ≤ Q₁.im) (hre2 : P₂.re ≤ w.re) (him2 : P₂.im ≤ w.im)
    (hborder₁ : RectangleBorder z Q₁ ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hborder₂ : RectangleBorder P₂ w ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hmem₁ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle z Q₁ ↔ c ρ ≤ a))
    (hmem₂ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle P₂ w ↔ a ≤ c ρ))
    (hsplit : RectangleIntegral (logDeriv f) z w
        = RectangleIntegral (logDeriv f) z Q₁ + RectangleIntegral (logDeriv f) P₂ w) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  -- a zero on the cut line would contradict `hane`, so `f` misses the two new borders
  have hcut : ∀ ρ ∈ Rectangle z w, c ρ = a → f ρ ≠ 0 := fun ρ hρ ha hf0 ↦
    hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩) ha
  have hbd₁ : ∀ ρ ∈ RectangleBorder z Q₁, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₁ hρ).elim (hcut ρ (hsubR₁R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hbd₂ : ∀ ρ ∈ RectangleBorder P₂ w, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₂ hρ).elim (hcut ρ (hsubR₂R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hfin₁ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₁R.trans hsub) hz₀U hz₀
  have hfin₂ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₂R.trans hsub) hz₀U hz₀
  have hfeq1 : hfin₁.toFinset = hfin.toFinset.filter (fun ρ ↦ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₁ hsubR₁R _ fun ρ hρ hf0 ↦
      (hmem₁ ρ hρ).trans (hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩)).le_iff_lt
  have hfeq2 : hfin₂.toFinset = hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₂ hsubR₂R _ fun ρ hρ _ ↦ (hmem₂ ρ hρ).trans not_lt.symm
  have hpart : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).card
      + (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).card = hfin.toFinset.card :=
    Finset.card_filter_add_card_filter_not _
  -- each half misses at least one of `ρ₁, ρ₂`, so both have at most `N` zeros
  have hne1 : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).Nonempty := by
    rcases min_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, hm ▸ ha1⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, hm ▸ ha1⟩⟩
  have hne2 : (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).Nonempty := by
    rcases max_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, not_lt.mpr (hm ▸ ha2).le⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, not_lt.mpr (hm ▸ ha2).le⟩⟩
  have hcard1 : hfin₁.toFinset.card ≤ N := by rw [hfeq1]; have := hne2.card_pos; lia
  have hcard2 : hfin₂.toFinset.card ≤ N := by rw [hfeq2]; have := hne1.card_pos; lia
  rw [hsplit, ih (hsubR₁R.trans hsub) hre1 him1 hbd₁ hfin₁ hcard1,
    ih (hsubR₂R.trans hsub) hre2 him2 hbd₂ hfin₂ hcard2,
    hfeq1, hfeq2, ← mul_add, Finset.sum_filter_add_sum_filter_not]

/-- Auxiliary form of the rectangle residue-sum theorem, carrying an explicit bound `N` on the
number of zeros to enable induction on it. -/
private theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    ∀ (N : ℕ) {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  -- the base case: at most one zero, handled by the single-zero theorem
  have base : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ 1 →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
    fun hsub hre him hbd hfin hcard ↦
      rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton hf hsub hre him hbd hfin
        fun a ha b hb ↦ Finset.card_le_one.mp hcard a (hfin.mem_toFinset.mpr ha) b
          (hfin.mem_toFinset.mpr hb)
  intro N
  induction N with
  | zero =>
    intro z w hsub hre him hbd hfin hcard
    exact base hsub hre him hbd hfin (hcard.trans (Nat.zero_le 1))
  | succ N ih =>
    intro z w hsub hre him hbd hfin hcard
    by_cases hc1 : hfin.toFinset.card ≤ 1
    · exact base hsub hre him hbd hfin hc1
    · -- at least two zeros: subdivide
      obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne⟩ := Finset.one_lt_card_iff.mp (not_le.mp hc1)
      obtain ⟨hz1, hw1, hzi1, hwi1⟩ := (mem_Rect hre him ρ₁).mp (hfin.mem_toFinset.mp hρ₁).1
      obtain ⟨hz2, hw2, hzi2, hwi2⟩ := (mem_Rect hre him ρ₂).mp (hfin.mem_toFinset.mp hρ₂).1
      -- the boundary integrand is integrable regardless of the cut orientation
      have hbi : RectangleBorderIntegrable (logDeriv f)
          (↑z.re + ↑z.im * I) (↑w.re + ↑w.im * I) := by
        rw [Complex.re_add_im, Complex.re_add_im]
        exact (holomorphicOn_logDeriv hf
          ((rectangleBorder_subset_rectangle z w).trans hsub) hbd).continuousOn
            |>.rectangleBorder_integrable
      rcases ne_or_eq ρ₁.re ρ₂.re with hred | hreq
      · -- vertical cut at `re = a`
        obtain ⟨a, ha1, ha2, haS⟩ :=
          exists_mem_Ioo_not_mem_finset (S := hfin.toFinset.image Complex.re) hred
        have hza : z.re ≤ a := (lt_of_le_of_lt (le_min hz1 hz2) ha1).le
        have haw : a ≤ w.re := (lt_of_lt_of_le ha2 (max_le hw1 hw2)).le
        have hane : ∀ ρ ∈ hfin.toFinset, ρ.re ≠ a := fun ρ hρ h ↦
          haS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑a + ↑w.im * I : ℂ).re := by simpa using hza
        have him1 : z.im ≤ (↑a + ↑w.im * I : ℂ).im := by simpa using him
        have hre2 : (↑a + ↑z.im * I : ℂ).re ≤ w.re := by simpa using haw
        have him2 : (↑a + ↑z.im * I : ℂ).im ≤ w.im := by simpa using him
        have hsubR₁R : Rectangle z (↑a + ↑w.im * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simpa using haw) le_rfl him1 (by simp)
        have hsubR₂R : Rectangle (↑a + ↑z.im * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simpa using hza) hre2 le_rfl (by simp) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑a + ↑w.im * I) ↔ ρ.re ≤ a) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑a + ↑z.im * I) w ↔ a ≤ ρ.re) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralHSplit' (f := logDeriv f) (a := a)
          (Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.re) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ ha1 ha2 hane hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_vcut hza haw).1 (rectangleBorder_vcut hza haw).2 hmem₁ hmem₂ hsplit
      · -- horizontal cut at `im = b`
        obtain ⟨b, hb1, hb2, hbS⟩ := exists_mem_Ioo_not_mem_finset
          (S := hfin.toFinset.image Complex.im) (fun h ↦ hne (Complex.ext hreq h))
        have hzb : z.im ≤ b := (lt_of_le_of_lt (le_min hzi1 hzi2) hb1).le
        have hbw : b ≤ w.im := (lt_of_lt_of_le hb2 (max_le hwi1 hwi2)).le
        have hbne : ∀ ρ ∈ hfin.toFinset, ρ.im ≠ b := fun ρ hρ h ↦
          hbS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑w.re + ↑b * I : ℂ).re := by simpa using hre
        have him1 : z.im ≤ (↑w.re + ↑b * I : ℂ).im := by simpa using hzb
        have hre2 : (↑z.re + ↑b * I : ℂ).re ≤ w.re := by simpa using hre
        have him2 : (↑z.re + ↑b * I : ℂ).im ≤ w.im := by simpa using hbw
        have hsubR₁R : Rectangle z (↑w.re + ↑b * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simp) le_rfl him1 (by simpa using hbw)
        have hsubR₂R : Rectangle (↑z.re + ↑b * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simp) hre2 le_rfl (by simpa using hzb) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑w.re + ↑b * I) ↔ ρ.im ≤ b) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑z.re + ↑b * I) w ↔ b ≤ ρ.im) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralVSplit' (f := logDeriv f) (b := b)
          (Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.im) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ hb1 hb2 hbne hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_hcut hzb hbw).1 (rectangleBorder_hcut hzb hbw).2 hmem₁ hmem₂ hsplit

/-- For `f` analytic on a connected `U`
and not identically zero (witnessed by `z₀ ∈ U` with `f z₀ ≠ 0`), and a positively oriented
`Rectangle z w ⊆ U` on whose boundary `f` does not vanish, the boundary integral of `logDeriv f`
counts the zeros inside with multiplicity:
`RectangleIntegral (logDeriv f) z w = 2πi · ∑_{ρ ∈ Z} (meromorphicOrderAt f ρ).untopD 0`,
`Z = Rectangle z w ∩ {ρ | f ρ = 0}`. -/
theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
  rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux hf hU hz₀U hz₀ hfin.toFinset.card hsub hzw_re
    hzw_im hbd hfin le_rfl

/-! ### From the residue sum to the boundary argument variation -/

/-- The real part of the logarithmic-derivative integral, `Re ∫ φ'/φ = log ‖φ b‖ - log ‖φ a‖`
(the companion of `argVariation_eq_im_integral`). -/
theorem re_integral_div_eq_log_norm_sub {a b : ℝ} (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u ↦ φ' u / φ u) (Set.Icc a b)) :
    (∫ u in a..b, φ' u / φ u).re = Real.log ‖φ b‖ - Real.log ‖φ a‖ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
    (fun u hu ↦ (hg.hasDerivAt hu (hderiv u hu)).hasDerivWithinAt)
    (hint.intervalIntegrable_of_Icc hab)
  have hre : ∀ u ∈ Set.Icc a b, (g u).re = Real.log ‖φ u‖ := fun u hu ↦ by
    rw [← hg.2 u hu, Complex.norm_exp, Real.log_exp]
  rw [hftc, Complex.sub_re, hre b (Set.right_mem_Icc.mpr hab), hre a (Set.left_mem_Icc.mpr hab)]

/-- For `f` analytic and nonvanishing along the affine segment `P → Q`, the
argument variation of `f` along it is the imaginary part of the edge integral
`∫₀¹ logDeriv f (lineSeg P Q u) · (Q - P) du`, whose real part is `log ‖f Q‖ - log ‖f P‖`. -/
theorem argVariation_lineSeg_eq_im_integral {f : ℂ → ℂ} {P Q : ℂ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℂ f (lineSeg P Q u))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg P Q u) ≠ 0) :
    argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
        = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
      (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
        = Real.log ‖f Q‖ - Real.log ‖f P‖ := by
  have hγderiv : ∀ u : ℝ, HasDerivAt (lineSeg P Q) (Q - P) u := fun u ↦ by
    have h1 : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h := (h1.mul_const (Q - P)).const_add P
    rwa [one_mul] at h
  have hφcont : ContinuousOn (fun u ↦ f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (hf u hu).continuousAt.comp_continuousWithinAt (continuous_lineSeg P Q).continuousWithinAt
  have hderivφ : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u ↦ f (lineSeg P Q u)) (deriv f (lineSeg P Q u) * (Q - P)) u := fun u hu ↦
    ((hf u (Set.Ioo_subset_Icc_self hu)).differentiableAt.hasDerivAt).comp u (hγderiv u)
  have hint : ContinuousOn
      (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (((hf u hu).deriv.continuousAt.comp_continuousWithinAt
        (continuous_lineSeg P Q).continuousWithinAt).mul continuousWithinAt_const).div
      (hφcont u hu) (hne u hu)
  have heqint : (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u))
      = fun u ↦ logDeriv f (lineSeg P Q u) * (Q - P) := by
    funext u; simp only [logDeriv_apply, mul_div_right_comm]
  refine ⟨by rw [argVariation_eq_im_integral zero_le_one hφcont hne hderivφ hint, heqint], ?_⟩
  have h := re_integral_div_eq_log_norm_sub zero_le_one hφcont hne hderivφ hint
  rw [heqint] at h
  rw [h, lineSeg_one, lineSeg_zero]

/-- The counterclockwise boundary argument variation `Δ_{∂R} arg f` of `f` around the
rectangle with opposite corners `z, w`: the sum of the argument variations over the four oriented
edges (bottom, right, top, left), each parametrised over `[0, 1]` by `lineSeg`. -/
noncomputable def rectangleArgVariation (f : ℂ → ℂ) (z w : ℂ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u))

/-- Affine reparametrisation of an interval integral over `[t₁, t₂]` to `[0, 1]`. -/
private theorem integral_affine_param (F : ℝ → ℂ) (t₁ t₂ : ℝ) :
    ∫ t in t₁..t₂, F t
      = ∫ u in (0 : ℝ)..1, ((t₂ - t₁ : ℝ) : ℂ) * F (t₁ + u * (t₂ - t₁)) := by
  rcases eq_or_ne t₁ t₂ with h | h
  · subst h; simp
  · have hc : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have key : ∫ u in (0 : ℝ)..1, F (t₁ + u * (t₂ - t₁))
        = (t₂ - t₁)⁻¹ • ∫ t in t₁..t₂, F t := by
      have hk := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) F hc t₁
      simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hk
      exact (intervalIntegral.integral_congr (fun u _ ↦ by congr 1; ring)).trans hk
    rw [intervalIntegral.integral_const_mul, key, Complex.real_smul, Complex.ofReal_inv,
      ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]

/-- A horizontal edge of the rectangle, the integral `HIntegral g`, as a `lineSeg` edge
integral over `[0, 1]`. -/
private theorem hIntegral_eq_lineSeg (g : ℂ → ℂ) (x₁ x₂ y : ℝ) :
    HIntegral g x₁ x₂ y
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u) *
          ((↑x₂ + ↑y * I) - (↑x₁ + ↑y * I)) := by
  rw [HIntegral, integral_affine_param (fun t ↦ g (↑t + ↑y * I)) x₁ x₂]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u = ↑(x₁ + u * (x₂ - x₁)) + ↑y * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg]; push_cast; ring

/-- A vertical edge of the rectangle, the integral `VIntegral g`, as a `lineSeg` edge integral
over `[0, 1]`. -/
private theorem vIntegral_eq_lineSeg (g : ℂ → ℂ) (x y₁ y₂ : ℝ) :
    VIntegral g x y₁ y₂
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u) *
          ((↑x + ↑y₂ * I) - (↑x + ↑y₁ * I)) := by
  rw [VIntegral, integral_affine_param (fun t ↦ g (↑x + ↑t * I)) y₁ y₂,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u = ↑x + ↑(y₁ + u * (y₂ - y₁)) * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg, smul_eq_mul]; push_cast; ring

/-- For `u ∈ [0, 1]`, the affine combination `a + u * (b - a)` lies in the interval `[[a, b]]`. -/
theorem add_mul_sub_mem_uIcc {a b u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.uIcc a b := by
  rw [← segment_eq_uIcc, segment_eq_image' ℝ]
  exact ⟨u, hu, by simp [smul_eq_mul]⟩

/-- A horizontal `lineSeg` edge at height `c` between `re = a` and `re = b` stays in the
horizontal side `[[a, b]] ×ℂ {c}` for parameters in `[0, 1]`. -/
private theorem lineSeg_mem_horizontal {a b c : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑b + ↑c * I) u ∈ Set.uIcc a b ×ℂ ({c} : Set ℝ) := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simpa using add_mul_sub_mem_uIcc (a := a) (b := b) hu, by simp⟩

/-- A vertical `lineSeg` edge at abscissa `a` between `im = c` and `im = d` stays in the vertical
side `{a} ×ℂ [[c, d]]` for parameters in `[0, 1]`. -/
private theorem lineSeg_mem_vertical {a c d : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑a + ↑d * I) u ∈ ({a} : Set ℝ) ×ℂ Set.uIcc c d := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simp, by simpa using add_mul_sub_mem_uIcc (a := c) (b := d) hu⟩

/-- For `f` analytic on a
neighbourhood of `Rectangle z w` and nonvanishing on its border,
`RectangleIntegral (logDeriv f) z w = I · Δ_{∂R} arg f`. -/
theorem rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation {f : ℂ → ℂ} {U : Set ℂ}
    {z w : ℂ} (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) :
    RectangleIntegral (logDeriv f) z w = I * (rectangleArgVariation f z w : ℂ) := by
  -- the four edge integrals
  set I0 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u) *
    ((↑w.re + ↑z.im * I) - (↑z.re + ↑z.im * I)) with hI0
  set I1 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u) *
    ((↑w.re + ↑w.im * I) - (↑w.re + ↑z.im * I)) with hI1
  set I2 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u) *
    ((↑z.re + ↑w.im * I) - (↑w.re + ↑w.im * I)) with hI2
  set I3 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u) *
    ((↑z.re + ↑z.im * I) - (↑z.re + ↑w.im * I)) with hI3
  -- the side-integral lemma applied to each of the four edges, which lie on the border
  have edge : ∀ {P Q : ℂ},
      (∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg P Q u ∈ RectangleBorder z w) →
      argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
          = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
        (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
          = Real.log ‖f Q‖ - Real.log ‖f P‖ := fun {P Q} hmem ↦
    argVariation_lineSeg_eq_im_integral
      (fun u hu ↦ hf _ (hsub (rectangleBorder_subset_rectangle z w (hmem u hu))))
      (fun u hu ↦ hbd _ (hmem u hu))
  have e0 := edge fun u hu ↦ Or.inl (Or.inl (Or.inl (lineSeg_mem_horizontal hu)))
  have e1 := edge fun u hu ↦ Or.inr (lineSeg_mem_vertical hu)
  have e2 := edge fun u hu ↦
    Or.inl (Or.inr (by rw [Set.uIcc_comm z.re w.re]; exact lineSeg_mem_horizontal hu))
  have e3 := edge fun u hu ↦
    Or.inl (Or.inl (Or.inr (by rw [Set.uIcc_comm z.im w.im]; exact lineSeg_mem_vertical hu)))
  -- the rectangle integral is the sum of the four edge integrals
  have hsum : RectangleIntegral (logDeriv f) z w = I0 + I1 + I2 + I3 := by
    have h0 : HIntegral (logDeriv f) z.re w.re z.im = I0 := hIntegral_eq_lineSeg _ _ _ _
    have h1 : VIntegral (logDeriv f) w.re z.im w.im = I1 := vIntegral_eq_lineSeg _ _ _ _
    have h2 : HIntegral (logDeriv f) z.re w.re w.im = -I2 := by
      rw [HIntegral_symm, hIntegral_eq_lineSeg]
    have h3 : VIntegral (logDeriv f) z.re z.im w.im = -I3 := by
      rw [VIntegral_symm, vIntegral_eq_lineSeg]
    rw [RectangleIntegral, h0, h1, h2, h3]; ring
  -- real parts telescope to zero, imaginary parts assemble to the argument variation
  have hre : (I0 + I1 + I2 + I3).re = 0 := by
    rw [hI0, hI1, hI2, hI3]
    simp only [Complex.add_re, e0.2, e1.2, e2.2, e3.2]; ring
  have him : (I0 + I1 + I2 + I3).im = rectangleArgVariation f z w := by
    rw [hI0, hI1, hI2, hI3, rectangleArgVariation, e0.1, e1.1, e2.1, e3.1]
    simp only [Complex.add_im]
  exact hsum.trans (Complex.ext (by rw [hre]; simp) (by rw [him]; simp))

/-- The argument principle on a rectangle. For `f` analytic on a connected `U`, not
identically zero (witnessed by `z₀ ∈ U` with `f z₀ ≠ 0`), and a positively oriented
`Rectangle z w ⊆ U` on whose boundary `f` does not vanish, the number of zeros inside, counted
with multiplicity, is `(1/2π) · Δ_{∂R} arg f`. -/
theorem rectangle_zero_count_eq_argVariation {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ)
      = 1 / (2 * Real.pi) * rectangleArgVariation f z w := by
  have h2 := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub hbd
  rw [rectangleIntegral_logDeriv_eq_two_pi_I_sum hf hU hz₀U hz₀ hsub hzw_re hzw_im hbd hfin,
    show (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
      = ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ) by
      push_cast; rfl] at h2
  -- cancel the factor `I` and pass back to the reals
  have h3 : (I : ℂ) * (2 * (Real.pi : ℂ) *
      ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ))
      = I * (rectangleArgVariation f z w : ℂ) := by rw [← h2]; ring
  have h5 : 2 * Real.pi * (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ))
      = rectangleArgVariation f z w := by
    exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero h3
  rw [one_div, inv_mul_eq_div, eq_div_iff (by positivity : (2 * Real.pi) ≠ 0)]
  linear_combination h5

/-- For `f` analytic and nowhere zero on a neighbourhood `U` of `Rectangle z w`,
`Δ_{∂R} arg f = 0`. -/
theorem rectangleArgVariation_eq_zero_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ x ∈ U, f x ≠ 0) (hsub : Rectangle z w ⊆ U) :
    rectangleArgVariation f z w = 0 := by
  have heq := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub
    fun ρ hρ ↦ hne ρ (hsub (rectangleBorder_subset_rectangle z w hρ))
  rw [HolomorphicOn.vanishesOnRectangle (holomorphicOn_logDeriv hf (subset_refl U) hne) hsub] at heq
  exact_mod_cast (mul_eq_zero.mp heq.symm).resolve_left Complex.I_ne_zero

