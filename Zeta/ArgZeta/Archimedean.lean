/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.Growth
public import Zeta.RiemannXi
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The archimedean strip-difference integral

The archimedean factor `Λ_a(s) = ½ s(s-1) Γ_ℝ(s)` of `ξ(s) = Λ_a(s) ζ(s)`, and the strip
difference `A(½+d) - A(½)` of its log-modulus integral `A(a) = ∫_a^{a+d} log‖Λ_a(σ+it)‖ dσ`
(`sec:ll_arch`).

## Main definitions

- `logNormGammaArchimedean`: the integrand `log‖Λ_a(σ+it)‖`.

## Main results

- `logNormGammaArchimedean_strip_diff_ge` (`lem:ll_arch`): `A(½+d) - A(½) ≥ (d²/2) log t - C`
  for a `t`-independent `C`, `t ≥ 168π` and `0 < d ≤ 2`.
- `logNormGammaArchimedean_strip_diff_ge_tight` (`lem:ls_Ca`): the same with an explicit `C`.
-/
@[expose] public section


open Complex Filter Topology Set MeasureTheory

open scoped Real


/-- The archimedean log-modulus integrand `log‖½ s(s-1) Γ_ℝ(s)‖` evaluated at `s = σ + it`,
where `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` is `Complex.Gammaℝ`. -/
noncomputable def logNormGammaArchimedean (t σ : ℝ) : ℝ :=
  Real.log ‖(1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖

/-- Norm of a point on the vertical line `a + it`. -/
private lemma norm_ofReal_add_I_mul (a t : ℝ) :
    ‖(a : ℂ) + Complex.I * t‖ = Real.sqrt (a ^ 2 + t ^ 2) := by
  rw [mul_comm, Complex.norm_add_mul_I]

/-- A point on the line `σ + it` with `t ≠ 0` is not the pole `0` of `Λ`. -/
lemma archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)

/-- A point on the line `σ + it` with `t ≠ 0` is not the pole `1` of `Λ`. -/
lemma archLine_sub_one_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    (σ : ℂ) + Complex.I * t - 1 ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)

private lemma Gammaℝ_archLine_ne_zero {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_im_ne_zero (by simpa using ht)

/-- The line point `(σ+it)/2` rewritten with explicit real and imaginary parts. -/
private lemma archLine_div_two (σ t : ℝ) :
    ((σ : ℂ) + Complex.I * t) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

/-- The half-line point `(σ+it)/2` is never a non-positive integer when `t ≠ 0`: its imaginary
part is `t/2 ≠ 0`.  Feeds the `Complex.Gamma` differentiability/continuity side conditions. -/
private lemma archLine_div_two_ne_neg_natCast {t : ℝ} (ht : t ≠ 0) (σ : ℝ) (m : ℕ) :
    ((σ : ℂ) + Complex.I * t) / 2 ≠ -m := by
  intro hm
  rw [archLine_div_two] at hm
  apply ht
  have him := congrArg Complex.im hm
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.neg_im, Complex.natCast_im, mul_one, mul_zero, zero_add,
    add_zero] at him
  linarith

/-- `‖Γ_ℝ(σ + it)‖ = π^{-σ/2} · ‖Γ((σ+it)/2)‖`. -/
private lemma norm_Gammaℝ_archLine (σ t : ℝ) :
    ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      Real.pi ^ (-σ / 2) * ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2
  simp [neg_div]

/-- `log‖Γ_ℝ(σ + it)‖ = -(σ/2) log π + log‖Γ((σ+it)/2)‖` for `t ≠ 0`. -/
private lemma log_norm_Gammaℝ_archLine {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ =
      -(σ / 2) * Real.log Real.pi + Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpole := archLine_div_two_ne_neg_natCast ht σ
  rw [norm_Gammaℝ_archLine,
    Real.log_mul (by positivity) (norm_ne_zero_iff.2 (Complex.Gamma_ne_zero hpole)),
    Real.log_rpow Real.pi_pos]
  ring

/-- Expansion of the archimedean integrand into a sum of logarithms. -/
private lemma logNormGammaArchimedean_eq {t : ℝ} (ht : t ≠ 0) (σ : ℝ) :
    logNormGammaArchimedean t σ =
      Real.log (1 / 2) + Real.log ‖(σ : ℂ) + Complex.I * t‖ +
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ +
        Real.log ‖Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)‖ := by
  unfold logNormGammaArchimedean
  set z : ℂ := (σ : ℂ) + Complex.I * t with hz
  have hz_ne : ‖z‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_ne_zero ht σ)
  have hz1_ne : ‖z - 1‖ ≠ 0 := by rw [hz]; exact norm_ne_zero_iff.2 (archLine_sub_one_ne_zero ht σ)
  have hG_ne : ‖Complex.Gammaℝ z‖ ≠ 0 := by
    rw [hz]; exact norm_ne_zero_iff.2 (Gammaℝ_archLine_ne_zero ht σ)
  have e : (1 / 2 : ℂ) * (z * (z - 1)) * Complex.Gammaℝ z =
      (1 / 2 : ℂ) * z * (z - 1) * Complex.Gammaℝ z := by ring
  rw [e, norm_mul, norm_mul, norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [h12, Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) hz_ne) hz1_ne) hG_ne,
    Real.log_mul (mul_ne_zero (by norm_num) hz_ne) hz1_ne,
    Real.log_mul (by norm_num) hz_ne]

/-- Continuity of the complex archimedean factor along the line `σ + it` for `t ≠ 0`. -/
private lemma continuous_archFactor {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) *
      (((σ : ℂ) + Complex.I * t) - 1)) * Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
  have hline : Continuous (fun σ : ℝ ↦ (σ : ℂ) + Complex.I * t) := by fun_prop
  have hdiv : Continuous (fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2) := hline.div_const 2
  have hndiv : Continuous (fun σ : ℝ ↦ -((σ : ℂ) + Complex.I * t) / 2) := hline.neg.div_const 2
  have hG : Continuous (fun σ : ℝ ↦ Complex.Gammaℝ ((σ : ℂ) + Complex.I * t)) := by
    rw [continuous_iff_continuousAt]
    intro σ
    have hcpow : ContinuousAt
        (fun σ : ℝ ↦ (Real.pi : ℂ) ^ (-((σ : ℂ) + Complex.I * t) / 2)) σ :=
      (continuousAt_const_cpow (by exact_mod_cast Real.pi_ne_zero)).comp hndiv.continuousAt
    have hGamma : ContinuousAt
        (fun σ : ℝ ↦ Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)) σ :=
      ContinuousAt.comp (g := Complex.Gamma)
        (f := fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) / 2)
        (Complex.differentiableAt_Gamma _ (archLine_div_two_ne_neg_natCast ht σ)).continuousAt
        hdiv.continuousAt
    simp only [Complex.Gammaℝ_def]
    exact hcpow.mul hGamma
  exact (continuous_const.mul (hline.mul (hline.sub continuous_const))).mul hG

/-- Continuity of the archimedean integrand `σ ↦ log‖Λ_a(σ+it)‖` for `t ≠ 0`. -/
lemma continuous_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) :
    Continuous (fun σ : ℝ ↦ logNormGammaArchimedean t σ) := by
  rw [continuous_iff_continuousAt]
  intro σ
  have hne : (1 / 2 : ℂ) * (((σ : ℂ) + Complex.I * t) * (((σ : ℂ) + Complex.I * t) - 1)) *
      Complex.Gammaℝ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
    prefactor_ne_zero_of (archLine_ne_zero ht σ)
      (sub_ne_zero.mp (archLine_sub_one_ne_zero ht σ)) (Gammaℝ_archLine_ne_zero ht σ)
  exact (Real.continuousAt_log (by simpa using hne)).comp
    ((continuous_norm.comp (continuous_archFactor ht)).continuousAt)

/-- The archimedean integrand is interval-integrable on every interval, for `t ≠ 0`. -/
lemma intervalIntegrable_logNormGammaArchimedean {t : ℝ} (ht : t ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume a b :=
  (continuous_logNormGammaArchimedean ht).intervalIntegrable a b

/-- **Strip integral as a shifted interval integral.** For `a ≤ b` and any shift `s`,
`∫_{Ioo (a+s) (b+s)} f = ∫ x in a..b, f (x + s)`. -/
lemma intervalIntegral.Ioo_eq_comp_add_right (f : ℝ → ℝ) {a b s : ℝ} (hab : a ≤ b) :
    (∫ σ in Set.Ioo (a + s) (b + s), f σ) = ∫ x in a..b, f (x + s) := by
  rw [intervalIntegral.integral_comp_add_right f s,
    intervalIntegral.integral_of_le (by linarith : a + s ≤ b + s),
    integral_Ioc_eq_integral_Ioo]

/-- A two-sided Stirling bound on `log‖Γ((σ+it)/2)‖` along the line, on the range
`1/2 ≤ σ ≤ 1/2 + 2d` covering both width-`d` strips. The divergent `-(π/2)(t/2)` term is present
on both sides. -/
private lemma log_norm_Gamma_archLine_bounds {d : ℝ} (hd : 0 < d) :
    ∃ L₁ L₂ : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + 2 * d → ∀ t : ℝ, 2 ≤ t →
      L₁ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) ≤
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ∧
      Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ≤
        L₂ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) := by
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hbound⟩ :=
    norm_Gamma_vertical_le (a := 1 / 4) (b := 1 / 4 + d) (by norm_num) (by linarith)
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  refine ⟨Real.log c₁, Real.log c₂, fun σ hσ1 hσ2 t ht ↦ ?_⟩
  have ht2 : (0 : ℝ) < t / 2 := by linarith
  obtain ⟨hlo, hhi⟩ := hbound (σ / 2) (by linarith) (by linarith) (t / 2)
    (by rw [abs_of_pos ht2]; linarith)
  rw [← archLine_div_two σ t, abs_of_pos ht2] at hlo hhi
  -- taking logs turns `c · (t/2)^{σ/2-1/2} · e^{-(π/2)(t/2)}` into the claimed affine expression
  have hlog : ∀ c : ℝ, 0 < c →
      Real.log (c * (t / 2) ^ (σ / 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * (t / 2)))
        = Real.log c + (σ / 2 - 1 / 2) * Real.log (t / 2) + -(Real.pi / 2) * (t / 2) :=
    fun c hc ↦ by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_mul hc.ne' (by positivity),
        Real.log_rpow ht2, Real.log_exp]
  have hLpos : 0 < c₁ * (t / 2) ^ (σ / 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * (t / 2)) := by
    positivity
  have h₁ := Real.log_le_log hLpos hlo
  have h₂ := Real.log_le_log (lt_of_lt_of_le hLpos hlo) hhi
  rw [hlog c₁ hc₁] at h₁
  rw [hlog c₂ hc₂] at h₂
  exact ⟨by linarith, by linarith⟩

/-! ### The tight archimedean constant via horizontal differentiation

The tight constant `C_a = (d²/2) log 2π + (d/2) log 2 + d²/10⁴` (`≤ 4/5` at `d = 74/100`),
an order of magnitude below the Stirling-band constant of
`logNormGammaArchimedean_strip_diff_ge_of`. -/

/-- **Horizontal derivative of `log‖Γ((σ+it)/2)‖`.** For `t ≠ 0` and `σ > 0`,
`d/dσ log‖Γ((σ+it)/2)‖ = ½ Re ψ((σ+it)/2)`. -/
private lemma hasDerivAt_log_norm_Gamma_archLine_half {t : ℝ} (_ht : t ≠ 0) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖Complex.Gamma (((u : ℂ) + Complex.I * t) / 2)‖)
      (1 / 2 * (Complex.digamma (((σ : ℂ) + Complex.I * t) / 2)).re) σ := by
  have hpath : HasDerivAt (fun u : ℝ ↦ ((u : ℂ) + Complex.I * t) / 2) (1 / 2 : ℂ) σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).add_const (Complex.I * t)).div_const 2
  have hzpos : 0 < (((σ : ℂ) + Complex.I * t) / 2).re := by
    rw [Complex.div_ofNat_re, show ((σ : ℂ) + Complex.I * t).re = σ by simp]; linarith
  simpa [Complex.mul_re] using Complex.hasDerivAt_log_norm_Gamma_comp hpath hzpos

/-- **Pointwise digamma lower bound on the strip.** For `t ≥ 168π` and `1/2 ≤ u ≤ 9/2`,
`½ Re ψ((u+it)/2) ≥ ½ log(t/2) - 1/10⁴`. -/
private lemma half_re_digamma_archLine_ge {t : ℝ} (ht : 168 * Real.pi ≤ t)
    {u : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 9 / 2) :
    1 / 2 * Real.log (t / 2) - 1 / 10000 ≤
      1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  set z : ℂ := ((u : ℂ) + Complex.I * t) / 2 with hz
  have hzre : z.re = u / 2 := by rw [hz, Complex.div_ofNat_re]; simp
  have h2z : 2 * z = (u : ℂ) + Complex.I * t := by rw [hz]; ring
  -- (1) `‖z‖ ≥ t/2`, hence `Re Log z = log‖z‖ ≥ log(t/2)`
  have hnorm_ge : t / 2 ≤ ‖z‖ := by
    have h : t ≤ Real.sqrt (u ^ 2 + t ^ 2) := by
      have := Real.sqrt_le_sqrt (show t ^ 2 ≤ u ^ 2 + t ^ 2 by nlinarith [sq_nonneg u])
      rwa [Real.sqrt_sq ht0.le] at this
    rw [hz, norm_div, Complex.norm_ofNat, le_div_iff₀ (by norm_num),
      mul_comm (Complex.I) (t : ℂ), Complex.norm_add_mul_I]
    linarith
  have hznpos : 0 < ‖z‖ := by linarith
  have hlogz : Real.log (t / 2) ≤ (Complex.log z).re := by
    rw [Complex.log_re]; exact Real.log_le_log (by linarith) hnorm_ge
  -- (2) pole term `Re (2z)⁻¹ = u/(u²+t²) ≤ u/t²`
  have hpole_le : ((2 * z)⁻¹).re ≤ u / t ^ 2 := by
    rw [h2z, show ((u : ℂ) + Complex.I * t) = ((u : ℂ) + (t : ℂ) * Complex.I) by ring,
      Complex.inv_re, Complex.normSq_add_mul_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    gcongr
    nlinarith [sq_nonneg u]
  -- (3) `Re E ≥ -‖E‖ ≥ -C₀‖z‖⁻² ≥ -3/t²`, `C₀ = 1/12 + 3/(2π²·(1/4)) = 1/12 + 6/π² ≤ 3/4`
  set E : ℂ := Complex.digamma z - Complex.log z + (2 * z)⁻¹ with hE
  have hEbound := Complex.Stirling.norm_digamma_sub_log_le' (a := 1 / 4) (by norm_num) z
    (by rw [hzre]; linarith)
  rw [← hE, show ‖z‖ ^ (-(2 : ℤ)) = (‖z‖ ^ 2)⁻¹ by rw [zpow_neg]; norm_cast] at hEbound
  have hC₀ : 3 / (2 * π ^ 2 * (1 / 4)) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hzn2_le : (‖z‖ ^ 2)⁻¹ ≤ 4 / t ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hEre : -(3 / t ^ 2) ≤ E.re := by
    have h3 : (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹ ≤ 3 / t ^ 2 := by
      calc (1 / 12 + 3 / (2 * π ^ 2 * (1 / 4))) * (‖z‖ ^ 2)⁻¹
          ≤ 3 / 4 * (4 / t ^ 2) := mul_le_mul (by linarith) hzn2_le (by positivity) (by norm_num)
        _ = 3 / t ^ 2 := by ring
    linarith [neg_abs_le E.re, Complex.abs_re_le_norm E, hEbound, h3]
  -- assemble `Re ψ(z) = Re Log z - Re(2z)⁻¹ + Re E ≥ log(t/2) - (u + 3)/t² ≥ log(t/2) - 1/5000`
  have hψre : (Complex.digamma z).re = (Complex.log z).re - ((2 * z)⁻¹).re + E.re := by
    rw [hE]; simp only [Complex.add_re, Complex.sub_re]; ring
  have htail : u / t ^ 2 + 3 / t ^ 2 ≤ 2 * (1 / 10000) := by
    rw [show u / t ^ 2 + 3 / t ^ 2 = (u + 3) / t ^ 2 by ring, div_le_iff₀ (by positivity)]
    nlinarith [ht504, hu2]
  linarith [hlogz, hpole_le, hEre, hψre, htail]

/-- **Tight lower bound on the `Γ` strip difference.** For `t ≥ 168π`, `0 < d ≤ 2` and
`1/2 ≤ σ ≤ 1/2 + d`,
`log‖Γ((σ+d+it)/2)‖ - log‖Γ((σ+it)/2)‖ ≥ (d/2) log(t/2) - d/10⁴`. -/
private lemma logNormGamma_half_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2) {t : ℝ}
    (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - d / 10000 ≤
      Real.log ‖Complex.Gamma ((((σ + d : ℝ) : ℂ) + Complex.I * t) / 2)‖ -
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have htne : t ≠ 0 := by nlinarith
  have hσd : σ ≤ σ + d := by linarith
  -- the derivative `½ Re ψ((u+it)/2)` is `≥ ½ log(t/2) - 10⁻⁴` on the strip `[σ, σ+d] ⊂ (0, 9/2]`,
  -- so the mean-value inequality gives the claim with no integrability side conditions
  have hderiv : ∀ u ∈ Set.Icc σ (σ + d),
      HasDerivAt (fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
        (1 / 2 * (Complex.digamma (((u : ℂ) + Complex.I * t) / 2)).re) u :=
    fun u hu ↦ hasDerivAt_log_norm_Gamma_archLine_half htne (by linarith [hu.1])
  have hmvt := (convex_Icc σ (σ + d)).mul_sub_le_image_sub_of_le_deriv
    (f := fun v : ℝ ↦ Real.log ‖Complex.Gamma (((v : ℂ) + Complex.I * t) / 2)‖)
    (C := 1 / 2 * Real.log (t / 2) - 1 / 10000)
    (fun u hu ↦ (hderiv u hu).continuousAt.continuousWithinAt)
    (fun u hu ↦ (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu ↦ by
      rw [interior_Icc, Set.mem_Ioo] at hu
      rw [(hderiv u ⟨hu.1.le, hu.2.le⟩).deriv]
      exact half_re_digamma_archLine_ge ht (by linarith [hu.1]) (by linarith [hu.2]))
    σ (Set.left_mem_Icc.2 hσd) (σ + d) (Set.right_mem_Icc.2 hσd) hσd
  beta_reduce at hmvt
  push_cast at hmvt ⊢
  nlinarith [hmvt]

/-- **Reverse-triangle bounds for the two linear factors of the archimedean function.** Along the
line `s = σ + it`, the `s`-factor log-modulus is nondecreasing under the `d`-shift, and the
`(s-1)`-factor loses at most `½ log 2`. -/
lemma logNormGammaArchimedean_line_log_norm_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 2 ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    Real.log ‖(σ : ℂ) + Complex.I * t‖ ≤ Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t‖ ∧
    -(1 / 2 * Real.log 2) ≤
      Real.log ‖((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1‖ -
        Real.log ‖(σ : ℂ) + Complex.I * t - 1‖ := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2pos : (0 : ℝ) < t ^ 2 := pow_pos ht0 2
  refine ⟨?_, ?_⟩
  · -- E1 : log‖(σ+d)+it‖ - log‖σ+it‖ ≥ 0
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t = ((σ + d : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring, norm_ofReal_add_I_mul, norm_ofReal_add_I_mul]
    apply Real.log_le_log (Real.sqrt_pos.2 (by nlinarith [sq_nonneg σ]))
    apply Real.sqrt_le_sqrt
    nlinarith
  · -- E2 : log‖(σ+d)-1+it‖ - log‖σ-1+it‖ ≥ -(1/2)log2
    rw [show ((σ : ℂ) + (d : ℂ)) + Complex.I * t - 1 = ((σ + d - 1 : ℝ) : ℂ) + Complex.I * t by
        push_cast; ring,
      show (σ : ℂ) + Complex.I * t - 1 = ((σ - 1 : ℝ) : ℂ) + Complex.I * t by push_cast; ring,
      norm_ofReal_add_I_mul, norm_ofReal_add_I_mul, Real.log_sqrt (by positivity),
      Real.log_sqrt (by positivity)]
    have hlow : Real.log (t ^ 2) ≤ Real.log ((σ + d - 1) ^ 2 + t ^ 2) :=
      Real.log_le_log ht2pos (by nlinarith [sq_nonneg (σ + d - 1)])
    have hhigh : Real.log ((σ - 1) ^ 2 + t ^ 2) ≤ Real.log (2 * t ^ 2) := by
      apply Real.log_le_log (by nlinarith [sq_nonneg (σ - 1)])
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - (σ - 1))
          (by linarith : (0 : ℝ) ≤ 2 + (σ - 1)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ t - 2) (by linarith : (0 : ℝ) ≤ t + 2)]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhigh
    rw [Real.log_pow] at hlow
    push_cast at hlow hhigh
    nlinarith [hlow, hhigh]

/-- **Tight pointwise lower bound for the shifted archimedean integrand difference.** The
band-free counterpart of `logNormGammaArchimedean_diff_ge`, with no Stirling constants `L₁, L₂`
in the bound. -/
lemma logNormGammaArchimedean_diff_ge_tight {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {t : ℝ} (ht : 168 * Real.pi ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - (d / 2) * Real.log Real.pi - 1 / 2 * Real.log 2 - d / 10000 ≤
      logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht2 : (2 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by nlinarith
  rw [logNormGammaArchimedean_eq htne (σ + d), logNormGammaArchimedean_eq htne σ,
    log_norm_Gammaℝ_archLine htne (σ + d), log_norm_Gammaℝ_archLine htne σ]
  push_cast
  -- E1/E2 : the `s` and `(s-1)` linear-factor log-modulus differences
  obtain ⟨hE1, hE2⟩ := logNormGammaArchimedean_line_log_norm_diff_ge hd hd' ht2 hσ1 hσ2
  -- E3 : tight Γ difference via FTC
  have hGamma := logNormGamma_half_diff_ge hd hd' ht hσ1 hσ2
  push_cast at hGamma
  nlinarith [hE1, hE2, hGamma]

/-- Pointwise lower bound for the shifted archimedean integrand difference, in terms of any pair
of Stirling constants `L₁, L₂`. -/
lemma logNormGammaArchimedean_diff_ge {d : ℝ} (hd : 0 < d) (hd' : d ≤ 2)
    {L₁ L₂ : ℝ}
    (hL : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + 2 * d → ∀ t : ℝ, 2 ≤ t →
      L₁ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) ≤
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ∧
      Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ≤
        L₂ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2))
    {t : ℝ} (ht : 2 ≤ t) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + d) :
    (d / 2) * Real.log (t / 2) - (d / 2) * Real.log Real.pi - 1 / 2 * Real.log 2 + (L₁ - L₂) ≤
      logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ := by
  have htne : t ≠ 0 := by linarith
  -- expand both integrands
  rw [logNormGammaArchimedean_eq htne (σ + d), logNormGammaArchimedean_eq htne σ,
    log_norm_Gammaℝ_archLine htne (σ + d), log_norm_Gammaℝ_archLine htne σ]
  push_cast
  -- E1/E2 : the `s` and `(s-1)` linear-factor log-modulus differences
  obtain ⟨hE1, hE2⟩ := logNormGammaArchimedean_line_log_norm_diff_ge hd hd' ht hσ1 hσ2
  -- E3 : Gamma part
  obtain ⟨_, hup⟩ := hL σ hσ1 (by linarith) t ht
  obtain ⟨hlo, _⟩ := hL (σ + d) (by linarith) (by linarith) t ht
  push_cast at hlo hup
  nlinarith [hE1, hE2, hlo, hup]

/-- **Constant-lower-bound strip-difference scaffold.** If the shifted archimedean integrand
difference is `≥ G` pointwise on the strip `[1/2, 1/2+d]`, then the strip difference
`A(½+d) - A(½)` is `≥ d · G`. -/
private lemma logNormGammaArchimedean_strip_diff_ge_of_pointwise {d G : ℝ} (hd : 1 / 2 < d)
    {t : ℝ} (htne : t ≠ 0)
    (hpt : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + d →
      G ≤ logNormGammaArchimedean t (σ + d) - logNormGammaArchimedean t σ) :
    d * G ≤
      (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
        ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  have hab : (1 / 2 : ℝ) ≤ 1 / 2 + d := by linarith
  -- convert the two strip integrals to interval integrals and shift the first
  have hshift : (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t (σ + d) := by
    rw [show (1 / 2 + 2 * d : ℝ) = (1 / 2 + d) + d by ring]
    exact intervalIntegral.Ioo_eq_comp_add_right
      (fun σ ↦ logNormGammaArchimedean t σ) (a := 1 / 2) (b := 1 / 2 + d) (s := d) hab
  have h1 : (∫ σ in Set.Ioo (1 / 2 : ℝ) (1 / 2 + d), logNormGammaArchimedean t σ) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), logNormGammaArchimedean t σ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Ioc_eq_integral_Ioo]
  rw [hshift, h1]
  -- the integrand difference is interval-integrable
  have hint1 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t (σ + d)) volume
      (1 / 2) (1 / 2 + d) :=
    ((continuous_logNormGammaArchimedean htne).comp (by fun_prop)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun σ : ℝ ↦ logNormGammaArchimedean t σ) volume
      (1 / 2) (1 / 2 + d) := intervalIntegrable_logNormGammaArchimedean htne _ _
  rw [← intervalIntegral.integral_sub hint1 hint2]
  -- lower-bound by the constant integral `∫ G = d · G`
  have hmono : (∫ _σ in (1 / 2 : ℝ)..(1 / 2 + d), G) ≤
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + d), (logNormGammaArchimedean t (σ + d) -
        logNormGammaArchimedean t σ) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const (hint1.sub hint2)
    intro σ hσ
    rw [Set.mem_Icc] at hσ
    exact hpt σ hσ.1 hσ.2
  rwa [intervalIntegral.integral_const, smul_eq_mul,
    show (1 / 2 + d - 1 / 2 : ℝ) = d by ring] at hmono

/-- **Parametric archimedean strip-difference bound.** Given any pair of Stirling constants
`L₁, L₂` realising the two-sided bound on `log‖Γ((σ+it)/2)‖`, the strip difference is bounded
below by `(d²/2) log t - C` with the explicit
`C = (d²/2)(log 2 + log π) + (d/2) log 2 + d(L₂ - L₁)`. -/
theorem logNormGammaArchimedean_strip_diff_ge_of {d L₁ L₂ : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2)
    (hL : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 / 2 + 2 * d → ∀ t : ℝ, 2 ≤ t →
      L₁ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2) ≤
        Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ∧
      Real.log ‖Complex.Gamma (((σ : ℂ) + Complex.I * t) / 2)‖ ≤
        L₂ + (σ / 2 - 1 / 2) * Real.log (t / 2) - Real.pi / 2 * (t / 2)) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t -
          ((d ^ 2 / 2) * (Real.log 2 + Real.log Real.pi) + (d / 2) * Real.log 2 + d * (L₂ - L₁)) ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  intro t ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have ht2 : (2 : ℝ) ≤ t := by linarith
  have htne : t ≠ 0 := by linarith
  -- the pointwise scaffold gives `d · G ≤ A(½+d) - A(½)` with `G` the pointwise diff bound
  have key := logNormGammaArchimedean_strip_diff_ge_of_pointwise hd htne
    (fun σ hσ1 hσ2 ↦ logNormGammaArchimedean_diff_ge (by linarith) hd' hL ht2 hσ1 hσ2)
  -- algebra: d · G = (d²/2) log t - C
  have hlogt : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div htne (by norm_num)]
  rw [hlogt] at key
  nlinarith [key]

/-- **Tight archimedean strip-difference bound** (`lem:ls_Ca`). The strip difference
`A(½+d) - A(½)` is bounded below by `(d²/2) log t - C_a` with the explicit
`C_a = (d²/2)(log 2 + log π) + (d/2) log 2 + d²/10⁴` (`≤ 4/5` at `d = 74/100`), carrying no
Stirling band width. -/
theorem logNormGammaArchimedean_strip_diff_ge_tight {d : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2) :
    ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t -
          ((d ^ 2 / 2) * (Real.log 2 + Real.log Real.pi) + (d / 2) * Real.log 2 + d ^ 2 / 10000) ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  intro t ht
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ht504 : (504 : ℝ) ≤ t := by nlinarith
  have htne : t ≠ 0 := by linarith
  -- the pointwise scaffold gives `d · G ≤ A(½+d) - A(½)` with `G` the tight pointwise diff bound
  have key := logNormGammaArchimedean_strip_diff_ge_of_pointwise hd htne
    (fun σ hσ1 hσ2 ↦ logNormGammaArchimedean_diff_ge_tight (by linarith) hd' ht hσ1 hσ2)
  have hlogt : Real.log (t / 2) = Real.log t - Real.log 2 := by
    rw [Real.log_div htne (by norm_num)]
  rw [hlogt] at key
  nlinarith [key]

/-- **Archimedean strip-difference bound** (`lem:ll_arch`). With
`A(a) := ∫_a^{a+d} log‖½ s(s-1) Γ_ℝ(s)‖ dσ` along `s = σ + it`, there is a `t`-independent
constant `C` with `A(½+d) - A(½) ≥ (d²/2) log t - C` for all `t ≥ 168π`. -/
theorem logNormGammaArchimedean_strip_diff_ge {d : ℝ} (hd : 1 / 2 < d) (hd' : d ≤ 2) :
    ∃ C : ℝ, ∀ t : ℝ, 168 * Real.pi ≤ t →
      (d ^ 2 / 2) * Real.log t - C ≤
        (∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d), logNormGammaArchimedean t σ) -
          ∫ σ in Set.Ioo (1 / 2) (1 / 2 + d), logNormGammaArchimedean t σ := by
  obtain ⟨L₁, L₂, hL⟩ := log_norm_Gamma_archLine_bounds (by linarith : (0 : ℝ) < d)
  exact ⟨_, logNormGammaArchimedean_strip_diff_ge_of hd hd' hL⟩

