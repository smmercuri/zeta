/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Stirling
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Euler–Maclaurin (Stirling) expansion of `log Γ`

The Stirling approximant `S_M` of `log Γ`, the improper `log Γ` remainder `ρ_M` and its explicit
arbitrary-order bound, together with the real-axis Stirling anchor.

The real-axis material lives in the sibling namespace `Real.Stirling`: it is about
`Real.log (Real.Gamma ·)`, not about the complex branch `Complex.logGamma`.

## Main definitions

- `Complex.Stirling.logGammaStirling`: the Stirling approximant
  `S_M(w) = (w - ½) Log w - w + ½ log(2π) + ∑_{k=1}^M B_{2k}/(2k(2k-1)) w^{1-2k}`.
- `Complex.Stirling.logGammaRemainderIoi`: the improper `log Γ` remainder
  `ρ_M(w) = ∫_0^∞ R^ψ_{2M+1}(w+τ) dτ`.
- `Real.Stirling.stirlingRef`: the real Stirling reference `(x-½) log x - x + ½ log(2π)`.

## Main results

- `Complex.Stirling.hasDerivAt_logGammaStirling`:
  `S_M' = Log w - 1/(2w) - ∑ B_{2k}/(2k) w^{-2k}`.
- `Complex.Stirling.norm_logGammaRemainderIoi_le`:
  `‖ρ_M(w)‖ ≤ (2M+1)!/(2M(2π)^{2M}) · (Re w)^{-2M}`.
- `Complex.Stirling.norm_logGammaRemainderIoi_le'`: the `‖w‖`-form variant
  `‖ρ_M(w)‖ ≤ (2M+1)! 2^{2M+1}/(2M(2π)^{2M}) · ‖w‖^{-2M}`, which, unlike the above, decays along
  a vertical line.
- `Complex.Stirling.logGammaStirling_two`: the order-`2` approximant with its Bernoulli
  coefficients evaluated.
- `Real.Stirling.tendsto_log_Gamma_sub_stirlingRef_atTop`: the real-axis Stirling anchor
  `log Γ(x) - r(x) → 0` as `x → +∞`, for `r = stirlingRef`.
-/
@[expose] public section


open MeasureTheory Filter
open scoped Topology Nat Real

namespace Complex.Stirling

/-- **Stirling approximant of `log Γ`:**
`S_M(w) = (w - ½) Log w - w + ½ log(2π) + ∑_{k=1}^M B_{2k}/(2k(2k-1)) w^{1-2k}`, where `Log` is the
principal complex logarithm. -/
noncomputable def logGammaStirling (M : ℕ) (w : ℂ) : ℂ :=
  (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)
    + ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * w ^ (1 - 2 * (k : ℤ))

/-- **`S_M` is a primitive of the digamma partial sum.** For `Re w > 0`,
`S_M'(w) = Log w - 1/(2w) - ∑_{k=1}^M B_{2k}/(2k) w^{-2k}`. -/
theorem hasDerivAt_logGammaStirling {M : ℕ} {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (logGammaStirling M)
      (Complex.log w - (2 * w)⁻¹
        - ∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * w ^ (-(2 * k : ℤ))) w := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos hw
  have hwslit : w ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hw)
  -- derivative of the smooth part `(w - ½) Log w - w + C`
  have hlog : HasDerivAt Complex.log w⁻¹ w := Complex.hasDerivAt_log hwslit
  have hid : HasDerivAt (fun z : ℂ ↦ z - 1 / 2) 1 w := (hasDerivAt_id w).sub_const _
  have hT1 : HasDerivAt (fun z : ℂ ↦ (z - 1 / 2) * Complex.log z)
      (1 * Complex.log w + (w - 1 / 2) * w⁻¹) w := hid.mul hlog
  -- derivative of the Bernoulli sum
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)) * z ^ (1 - 2 * (k : ℤ)))
      (∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
          * ((1 - 2 * (k : ℤ) : ℤ) * w ^ ((1 - 2 * (k : ℤ)) - 1))) w := by
    apply HasDerivAt.fun_sum
    intro k _
    exact (hasDerivAt_zpow (1 - 2 * (k : ℤ)) w (Or.inl hw0)).const_mul
      ((bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1)))
  have hderiv := ((hT1.sub (hasDerivAt_id w)).add_const
      ((1 / 2 : ℂ) * (Real.log (2 * π) : ℂ))).add hsum
  refine hderiv.congr_deriv ?_
  -- reconcile the computed derivative with the truncated digamma series
  have hscal : 1 * Complex.log w + (w - 1 / 2) * w⁻¹ - 1 = Complex.log w - (2 * w)⁻¹ := by
    field_simp
    ring
  have hsumeq : (∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℂ) / (2 * (k : ℂ) * (2 * (k : ℂ) - 1))
          * ((1 - 2 * (k : ℤ) : ℤ) * w ^ ((1 - 2 * (k : ℤ)) - 1)))
      = -∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * w ^ (-(2 * k : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hk2 : 2 * (k : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show 2 * k ≠ 1 by lia))
    rw [show (1 - 2 * (k : ℤ)) - 1 = -(2 * k : ℤ) by ring]
    push_cast
    field_simp
    ring
  rw [hscal, hsumeq]
  ring

/-- **Improper `log Γ` remainder** `ρ_M(w) = ∫_0^∞ R^ψ_{2M+1}(w+τ) dτ`, the ray-integral of the
digamma remainder `digammaRemainderIoi`. -/
noncomputable def logGammaRemainderIoi (M : ℕ) (w : ℂ) : ℂ :=
  ∫ τ in Set.Ioi (0 : ℝ), digammaRemainderIoi (w + (τ : ℂ)) (2 * M + 1)

/-- `x ^ (-(n : ℝ)) = x ^ (-(n : ℤ))`. -/
private theorem rpow_neg_natCast_eq_zpow (x : ℝ) (n : ℕ) :
    x ^ (-(n : ℝ)) = x ^ (-(n : ℤ)) := by
  rw [show (-(n : ℝ)) = ((-(n : ℤ) : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]

/-- The shifted improper power integral `∫_0^∞ (τ + σ)^a dτ = -σ^{a+1}/(a+1)` for `a < -1`,
`σ > 0`. -/
private theorem integral_Ioi_add_rpow_of_lt {a σ : ℝ} (ha : a < -1) (hσ : 0 < σ) :
    ∫ τ in Set.Ioi (0 : ℝ), (τ + σ) ^ a = -σ ^ (a + 1) / (a + 1) := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ ↦ (t + σ) ^ (a + 1) / (a + 1)) ((x + σ) ^ a) x := by
    intro x hx
    have hxσ : (0 : ℝ) < x + σ := by linarith [Set.mem_Ici.mp hx]
    have ha1 : a + 1 ≠ 0 := by linarith
    have h := (((hasDerivAt_id x).add_const σ).rpow_const (p := a + 1)
      (Or.inl hxσ.ne')).div_const (a + 1)
    have hval : (1 : ℝ) * (a + 1) * (id x + σ) ^ (a + 1 - 1) / (a + 1) = (x + σ) ^ a := by
      rw [id_eq, show a + 1 - 1 = a by ring]
      field_simp
    rwa [hval] at h
  have hint : IntegrableOn (fun τ : ℝ ↦ (τ + σ) ^ a) (Set.Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt ha (by linarith)
  have ht : Tendsto (fun t : ℝ ↦ (t + σ) ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ σ tendsto_id) |>.div_const _
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd hint ht using 1
  simp [neg_div]

/-- The right-hand side of `norm_logGammaRemainderIoi_le`:
`(2M+1)!/(2M(2π)^{2M}) · (Re w)^{-2M}`. -/
noncomputable abbrev logGammaRemainderBound (M : ℕ) (w : ℂ) : ℝ :=
  ((2 * M + 1)! : ℝ) / (2 * M * (2 * π) ^ (2 * M)) * w.re ^ (-(2 * M : ℤ))

/-- The right-hand side of `norm_logGammaRemainderIoi_le'`:
`(2M+1)! · 2^{2M+1}/(2M(2π)^{2M}) · ‖w‖^{-2M}`. -/
noncomputable abbrev logGammaRemainderNormBound (M : ℕ) (w : ℂ) : ℝ :=
  ((2 * M + 1)! : ℝ) * 2 ^ (2 * M + 1) / (2 * M * (2 * π) ^ (2 * M)) * ‖w‖ ^ (-(2 * M : ℤ))

/-- **The `log Γ` remainder bound against an arbitrary majorant of the ray** `τ ↦ w + τ`. The
shared core of `norm_logGammaRemainderIoi_le` (`κ = 1`, `σ = Re w`) and
`norm_logGammaRemainderIoi_le'` (`κ = 2`, `σ = ‖w‖`). -/
private theorem norm_logGammaRemainderIoi_le_of_div_le {M : ℕ} (hM : 1 ≤ M) {w : ℂ}
    (hw : 0 < w.re) {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hle : ∀ τ ∈ Set.Ioi (0 : ℝ), (τ + σ) / κ ≤ ‖w + (τ : ℂ)‖) :
    ‖logGammaRemainderIoi M w‖
      ≤ ((2 * M + 1)! : ℝ) * κ ^ (2 * M + 1) / (2 * M * (2 * π) ^ (2 * M))
          * σ ^ (-(2 * M : ℤ)) := by
  set p : ℕ := 2 * M + 1 with hp
  have hp2 : 2 ≤ p := by lia
  have hp1 : p - 1 = 2 * M := by lia
  set C : ℝ := (p ! : ℝ) / (2 * π) ^ (p - 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hpR : (-(p : ℝ)) < -1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  -- the integrable majorant `g τ = C κ^p (τ + σ)^{-p}`
  set g : ℝ → ℝ := fun τ ↦ C * κ ^ p * (τ + σ) ^ (-(p : ℝ)) with hgdef
  have hgint : IntegrableOn g (Set.Ioi 0) :=
    (integrableOn_add_rpow_Ioi_of_lt hpR (by linarith)).const_mul (C * κ ^ p)
  -- pointwise domination of the integrand's norm by `g`
  have hbound : ∀ τ ∈ Set.Ioi (0 : ℝ),
      ‖digammaRemainderIoi (w + (τ : ℂ)) p‖ ≤ g τ := by
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := hτ
    have hre : 0 < (w + (τ : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hnpos : 0 < (τ + σ) / κ := by positivity
    have h1 := norm_digammaRemainderIoi_le' (w + (τ : ℂ)) hre p (by lia)
    rw [← hCdef] at h1
    have hmono : ‖w + (τ : ℂ)‖ ^ (-(p : ℝ)) ≤ ((τ + σ) / κ) ^ (-(p : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hnpos (hle τ hτ) (neg_nonpos.mpr (by positivity))
    have hdiv : ((τ + σ) / κ) ^ (-(p : ℝ)) = κ ^ p * (τ + σ) ^ (-(p : ℝ)) := by
      rw [Real.div_rpow (by positivity) hκ.le, Real.rpow_neg hκ.le, Real.rpow_natCast,
        div_eq_mul_inv, inv_inv, mul_comm]
    calc ‖digammaRemainderIoi (w + (τ : ℂ)) p‖
        ≤ C * ‖w + (τ : ℂ)‖ ^ (-(p : ℤ)) := h1
      _ = C * ‖w + (τ : ℂ)‖ ^ (-(p : ℝ)) := by rw [← rpow_neg_natCast_eq_zpow]
      _ ≤ C * (κ ^ p * (τ + σ) ^ (-(p : ℝ))) :=
          mul_le_mul_of_nonneg_left (hdiv ▸ hmono) hC0
      _ = g τ := by simp only [hgdef]; ring
  -- assemble via the norm-integral bound, then evaluate the majorant integral
  calc ‖logGammaRemainderIoi M w‖
      ≤ ∫ τ in Set.Ioi (0 : ℝ), g τ := by
        rw [logGammaRemainderIoi, ← hp]
        refine norm_integral_le_of_norm_le hgint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ using hbound τ hτ
    _ = C * κ ^ p * (σ ^ (-(2 * M : ℤ)) / (2 * (M : ℝ))) := by
        rw [hgdef, integral_const_mul, integral_Ioi_add_rpow_of_lt hpR hσ,
          show (-(p : ℝ)) + 1 = -(2 * (M : ℝ)) by rw [hp]; push_cast; ring,
          show σ ^ (-(2 * (M : ℝ))) = σ ^ (-(2 * M : ℤ)) by
            rw [show (-(2 * (M : ℝ))) = ((-(2 * M : ℤ) : ℤ) : ℝ) by push_cast; ring,
              Real.rpow_intCast],
          neg_div_neg_eq]
    _ = _ := by rw [hCdef, hp1, hp]; ring

/-- **Explicit arbitrary-order `log Γ` remainder bound.** For every `M ≥ 1` and every `w` with
`Re w > 0`, `‖ρ_M(w)‖ ≤ (2M+1)!/(2M(2π)^{2M}) · (Re w)^{-2M}`. -/
theorem norm_logGammaRemainderIoi_le {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    ‖logGammaRemainderIoi M w‖ ≤ logGammaRemainderBound M w := by
  refine (norm_logGammaRemainderIoi_le_of_div_le hM hw hw zero_lt_one fun τ hτ ↦ ?_).trans_eq ?_
  · rw [div_one]
    have hτ0 : (0 : ℝ) < τ := hτ
    have := Complex.re_le_norm (w + (τ : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  · simp [logGammaRemainderBound]

/-- **The `log Γ` remainder bound in `‖w‖` form**, which, unlike `norm_logGammaRemainderIoi_le`,
decays along a vertical line. Its extra factor `2^{2M+1}` cannot be dropped: at `w = i s` already
`∫_0^∞ ‖w + τ‖^{-5} dτ = (2/3) s^{-4} > (1/4) s^{-4}`. -/
theorem norm_logGammaRemainderIoi_le' {M : ℕ} (hM : 1 ≤ M) {w : ℂ} (hw : 0 < w.re) :
    ‖logGammaRemainderIoi M w‖ ≤ logGammaRemainderNormBound M w := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hw)
  refine norm_logGammaRemainderIoi_le_of_div_le hM hw hw0 two_pos fun τ hτ ↦ ?_
  have hτ0 : (0 : ℝ) < τ := hτ
  -- `‖w‖ ≤ ‖w + τ‖`, since translating right increases the real part in absolute value
  have h1 : ‖w‖ ≤ ‖w + (τ : ℂ)‖ := by
    have hsq : ‖w‖ ^ 2 ≤ ‖w + (τ : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      nlinarith
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this
  -- `τ ≤ Re w + τ ≤ ‖w + τ‖`
  have h2 : τ ≤ ‖w + (τ : ℂ)‖ := by
    have := Complex.re_le_norm (w + (τ : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  linarith

/-- **The order-`2` Stirling approximant**, with its Bernoulli coefficients `B₂ = 1/6` and
`B₄ = -1/30` evaluated. -/
theorem logGammaStirling_two (w : ℂ) :
    logGammaStirling 2 w
      = (w - 1 / 2) * Complex.log w - w + (1 / 2 : ℂ) * (Real.log (2 * π) : ℂ)
        + 1 / 12 * w⁻¹ - 1 / 360 * (w ^ 3)⁻¹ := by
  have hb2 : ((bernoulli 2 : ℚ) : ℂ) = 1 / 6 := by rw [bernoulli_two]; norm_num
  have hb4 : ((bernoulli 4 : ℚ) : ℂ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; norm_num
  rw [logGammaStirling, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  rw [show ((1 : ℤ) - 2 * ((1 : ℕ) : ℤ)) = -1 by norm_num,
    show ((1 : ℤ) - 2 * ((2 : ℕ) : ℤ)) = -(3 : ℕ) by norm_num,
    zpow_neg_one, zpow_neg, zpow_natCast, hb2, hb4]
  push_cast
  ring

end Complex.Stirling

/-! ### The real-axis Stirling anchor -/

namespace Real.Stirling

/-- The real Stirling reference `r(x) = (x - ½) log x - x + ½ log(2π)`, the order-`0` Stirling
approximant of `log Γ` on the positive real axis. It is the `Real.log`-valued counterpart of
`Complex.Stirling.logGammaStirling 0`, kept separate to avoid threading the
`Complex.log`/`Real.log` bridge through the real arguments below. -/
noncomputable def stirlingRef (x : ℝ) : ℝ :=
  (x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * π)

/-- `r'(x) = log x - 1/(2x)` on `(0, ∞)`. -/
private theorem hasDerivAt_stirlingRef {x : ℝ} (hx : 0 < x) :
    HasDerivAt stirlingRef (Real.log x - 1 / (2 * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ (y - 1 / 2) * Real.log y)
      (1 * Real.log x + (x - 1 / 2) * x⁻¹) x :=
    ((hasDerivAt_id' (x := x)).sub_const (1 / 2)).mul (Real.hasDerivAt_log hx.ne')
  have h2 : HasDerivAt stirlingRef ((1 * Real.log x + (x - 1 / 2) * x⁻¹) - 1) x :=
    (h1.sub (hasDerivAt_id' (x := x))).add_const (1 / 2 * Real.log (2 * π))
  rwa [show (1 * Real.log x + (x - 1 / 2) * x⁻¹) - 1 = Real.log x - 1 / (2 * x) by
    field_simp; ring] at h2

/-- The majorant `δ(n) = log(n+1) - log(n-1) + 1/(2n)` controlling the fractional-part error
`|φ(x) - φ(⌊x⌋)|` of the anchor, where `φ = log Γ - r`. -/
private noncomputable def stirlingAnchorBound (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1) + 1 / (2 * (n : ℝ))

/-- `δ(n) → 0` as `n → ∞`. -/
private theorem tendsto_stirlingAnchorBound :
    Tendsto (fun n : ℕ ↦ stirlingAnchorBound n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1))
      atTop (𝓝 0) := by
    have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop)
      have h3 : Tendsto (fun n : ℕ ↦ 1 + 2 / ((n : ℝ) - 1)) atTop (𝓝 1) := by
        simpa using h2.const_add 1
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn1 : ((n : ℝ) - 1) ≠ 0 := by
        intro h; rw [sub_eq_zero] at h; linarith
      field_simp
      ring
    have hc := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hratio
    rw [Real.log_one] at hc
    refine hc.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hle : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
    rw [Function.comp_apply, Real.log_div h1 h2]
  have hinv : Tendsto (fun n : ℕ ↦ 1 / (2 * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop' (by norm_num) tendsto_natCast_atTop_atTop)
  simpa [stirlingAnchorBound] using hlog.add hinv

/-- **Integer Stirling anchor.** For natural `n`, `log Γ(n) - r(n) → 0`. -/
private theorem tendsto_log_Gamma_sub_stirlingRef_nat :
    Tendsto (fun n : ℕ ↦ Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n) - Real.log π / 2)
      atTop (𝓝 0) := by
    have hcont : Tendsto (fun n : ℕ ↦ Real.log (Stirling.stirlingSeq n))
        atTop (𝓝 (Real.log π / 2)) := by
      have h := (Real.continuousAt_log (x := √π) (by positivity)).tendsto.comp
        Stirling.tendsto_stirlingSeq_sqrt_pi
      rwa [Function.comp_def, Real.log_sqrt Real.pi_pos.le] at h
    simpa using hcont.sub_const (Real.log π / 2)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hΓpos : 0 < Real.Gamma (n : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < n by lia))
  have hfact : (n : ℝ) * Real.Gamma (n : ℝ) = (n ! : ℝ) := by
    rw [← Real.Gamma_add_one hn0]; exact_mod_cast Real.Gamma_nat_eq_factorial n
  have e1 : Real.log (Real.Gamma (n : ℝ)) = Real.log (n ! : ℝ) - Real.log (n : ℝ) := by
    have h := congrArg Real.log hfact
    rw [Real.log_mul hn0 hΓpos.ne'] at h
    linarith
  rw [Stirling.log_stirlingSeq_formula, e1, stirlingRef,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
    Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

/-- **Fractional-part control.** For `x ≥ 2` with `n := ⌊x⌋`, the anchor `φ = log Γ - r` satisfies
`|φ(x)| ≤ |φ(n)| + δ(n)`. -/
private theorem abs_log_Gamma_sub_stirlingRef_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (Real.Gamma x) - stirlingRef x|
      ≤ |Real.log (Real.Gamma (⌊x⌋₊ : ℝ)) - stirlingRef (⌊x⌋₊ : ℝ)| + stirlingAnchorBound ⌊x⌋₊ := by
  set n := ⌊x⌋₊
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_floor (by exact_mod_cast hx : ((2 : ℕ) : ℝ) ≤ x)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnm1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hax : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxa1 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogmono : Real.log ((n : ℝ) - 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hnm1pos (by linarith)
  have hbnd_nonneg : 0 ≤ stirlingAnchorBound n := by
    have : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
    simp only [stirlingAnchorBound]; linarith
  -- Gamma functional-equation differences at `n` and `n - 1`
  have hf1 : Real.log (Real.Gamma ((n : ℝ) + 1))
      = Real.log (n : ℝ) + Real.log (Real.Gamma (n : ℝ)) := by
    rw [Real.Gamma_add_one hnpos.ne', Real.log_mul hnpos.ne' (Real.Gamma_pos_of_pos hnpos).ne']
  have hnum : Real.log (Real.Gamma (n : ℝ)) - Real.log (Real.Gamma ((n : ℝ) - 1))
      = Real.log ((n : ℝ) - 1) := by
    have h := Real.Gamma_add_one (s := (n : ℝ) - 1) hnm1pos.ne'
    rw [show (n : ℝ) - 1 + 1 = (n : ℝ) by ring] at h
    rw [h, Real.log_mul hnm1pos.ne' (Real.Gamma_pos_of_pos hnm1pos).ne']; ring
  -- reduce to controlling `φ(x) - φ(n)`
  rw [← sub_le_iff_le_add']
  refine (abs_sub_abs_le_abs_sub _ _).trans ?_
  rcases hax.lt_or_eq with hlt | heq
  · -- main case `n < x`
    have hd0 : (0 : ℝ) < x - (n : ℝ) := by linarith
    -- upper: `log Γ(x) - log Γ(n) ≤ (x - n) log n`
    have hup := Real.convexOn_log_Gamma.secant_mono_aux2 hnpos
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (n : ℝ) + 1)) hlt hxa1
    simp only [Function.comp_apply] at hup
    rw [hf1, show (n : ℝ) + 1 - (n : ℝ) = 1 by ring, div_one, add_sub_cancel_right] at hup
    have hup' := (div_le_iff₀ hd0).mp hup
    -- lower: `(x - n) log (n - 1) ≤ log Γ(x) - log Γ(n)`
    have hlo := Real.convexOn_log_Gamma.slope_mono_adjacent hnm1pos
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < x)) (by linarith) hlt
    simp only [Function.comp_apply] at hlo
    rw [show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring, div_one, hnum] at hlo
    have hlo' := (le_div_iff₀ hd0).mp hlo
    -- MVT for the smooth reference on `[n, x]`
    have hcont : ContinuousOn stirlingRef (Set.Icc (n : ℝ) x) := fun t ht ↦
      (hasDerivAt_stirlingRef (by have := ht.1; linarith)).continuousAt.continuousWithinAt
    obtain ⟨ξ, ⟨hξlo, hξhi⟩, hξeq⟩ := exists_hasDerivAt_eq_slope stirlingRef
      (fun t ↦ Real.log t - 1 / (2 * t)) hlt hcont
      (fun t ht ↦ hasDerivAt_stirlingRef (by have := ht.1; linarith))
    have hξpos : 0 < ξ := by linarith
    have hQ : stirlingRef x - stirlingRef (n : ℝ)
        = (Real.log ξ - 1 / (2 * ξ)) * (x - (n : ℝ)) := by
      rw [hξeq, div_mul_cancel₀ _ hd0.ne']
    -- bounds on the mean-value derivative
    have hlogξlo : Real.log (n : ℝ) ≤ Real.log ξ := Real.log_le_log hnpos hξlo.le
    have hlogξhi : Real.log ξ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hξpos (by linarith)
    have hinvξ : 1 / (2 * ξ) ≤ 1 / (2 * (n : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hinvξ0 : (0 : ℝ) ≤ 1 / (2 * ξ) := by positivity
    have hQlo : (Real.log (n : ℝ) - 1 / (2 * (n : ℝ))) * (x - (n : ℝ))
        ≤ stirlingRef x - stirlingRef (n : ℝ) := by
      rw [hQ]; exact mul_le_mul_of_nonneg_right (by linarith) hd0.le
    have hQhi : stirlingRef x - stirlingRef (n : ℝ)
        ≤ Real.log ((n : ℝ) + 1) * (x - (n : ℝ)) := by
      rw [hQ]; exact mul_le_mul_of_nonneg_right (by linarith) hd0.le
    -- assemble the two-sided bound on `φ(x) - φ(n)`
    rw [abs_le, stirlingAnchorBound]
    refine ⟨?_, ?_⟩
    · nlinarith [hlo', hQhi, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (x - (n : ℝ)))
        (by linarith : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1))]
    · nlinarith [hup', hQlo, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (x - (n : ℝ)))
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)))]
  · rw [heq]; simpa using hbnd_nonneg

/-- **Real-axis Stirling anchor.** As `x → +∞`, `log Γ(x) - r(x) → 0`, where `r = stirlingRef`.
This is what pins the additive constant `½ log(2π)` of the Stirling expansion of `log Γ`. -/
theorem tendsto_log_Gamma_sub_stirlingRef_atTop :
    Tendsto (fun x : ℝ ↦ Real.log (Real.Gamma x) - stirlingRef x) atTop (𝓝 0) := by
  set M : ℕ → ℝ := fun n ↦
    |Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)| + stirlingAnchorBound n with hM
  have hMlim : Tendsto M atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ |Real.log (Real.Gamma (n : ℝ)) - stirlingRef (n : ℝ)|)
        atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using tendsto_log_Gamma_sub_stirlingRef_nat.norm
    simpa [hM] using h1.add tendsto_stirlingAnchorBound
  have hbnd : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.Gamma x) - stirlingRef x‖ ≤ M ⌊x⌋₊ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [Real.norm_eq_abs, hM]
    exact abs_log_Gamma_sub_stirlingRef_le hx
  exact squeeze_zero_norm' hbnd (hMlim.comp tendsto_nat_floor_atTop)

end Real.Stirling
