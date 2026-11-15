/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# The auxiliary integral `I(t)` and limiting behaviour of `ζ` towards `+∞`

The log-modulus line integral `I(t) = ∫_{1/2}^∞ log|ζ(σ + it)| dσ` underlying Lehman's bound for
`∫ S(t) dt`, the limiting behaviour of `ζ` and `arg ζ` along horizontal rays towards `+∞`, and the
shared `p`-series / sum-integral toolkit used throughout the chapter.

## Main definitions

- `logNormZetaIntegral`: the integral `I(t)` of `def:lb_I`.

## Main results

- `tendsto_riemannZeta_atTop_nhds_one`: `ζ(σ + it) → 1` as `σ → +∞`.
- `tendsto_arg_riemannZeta_atTop` (`lem:lb_arg_tendsto`): `arg ζ(σ + it) → 0` as `σ → +∞`.
- `integrableOn_log_norm_riemannZeta_Ioi` (`lem:lb_I_integrable`): the integrand of `I(t)` is
  integrable on `[1/2, ∞)`, away from the zeros of `ζ`.
- `neg_tsum_one_div_le_log_norm_riemannZeta`, `log_norm_riemannZeta_le_tsum_one_div`,
  `abs_log_norm_riemannZeta_le_tsum_one_div`: two-sided control of the integrand by the real
  `p`-series tail `ζ(σ) - 1 = ∑_n (n+2)^{-σ}`, for `σ > 1`.
- `logNormZetaIntegral_tail_ge` (`lem:ll_tail`): a `t`-independent lower bound for the tail
  `∫_{1/2+d}^∞ log|ζ(σ + it)| dσ` and for the strip `∫_{1/2+d}^{1/2+2d} log|ζ(σ + it)| dσ`.
-/
@[expose] public section


open Complex Filter Topology MeasureTheory

/-- **The log-modulus line integral** `I(t) = ∫_{1/2}^∞ log|ζ(σ + it)| dσ` of `def:lb_I`. -/
noncomputable def logNormZetaIntegral (t : ℝ) : ℝ :=
  ∫ σ in Set.Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖

/-! ## The shared `p`-series / sum-integral toolkit

The shifted `p`-series `∑_n (n + m)^{-a}` and its comparison with `∫ x^{-a}`, used throughout the
chapter. -/

/-- The shifted real `p`-series `∑_n ((n+2)^{-p})` is summable for `1 < p`; the `|·|`-free form of
mathlib's `Real.summable_one_div_nat_add_rpow`. -/
theorem Real.summable_one_div_nat_add_two_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ p) := by
  refine ((Real.summable_one_div_nat_add_rpow 2 p).mpr hp).congr (fun n ↦ ?_)
  rw [abs_of_nonneg (by positivity)]

/-- The map `x ↦ x^{-σ}` is antitone on `[a, b]` for `0 ≤ σ` and `0 < a`. -/
theorem Real.antitoneOn_rpow_neg_Icc {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    AntitoneOn (fun x : ℝ ↦ x ^ (-σ)) (Set.Icc a b) := fun x hx _ _ hxy ↦
  Real.rpow_le_rpow_of_nonpos (by simp only [Set.mem_Icc] at hx; linarith [hx.1]) hxy
    (neg_nonpos.mpr hσ)

/-- Pass a finite-window comparison `∫_{c}^{c+N} f ≤ ∑_{i<N} a(i+k)` to the improper integral and
the full series: `∫_{Ioi c} f ≤ ∑' n, a(n+k)`. -/
theorem Real.integral_Ioi_le_tsum_of_window {a : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hsum : Summable a) (hInt : IntegrableOn f (Set.Ioi c))
    (hcmp : ∀ N : ℕ, (∫ x in c..(c + (N : ℝ)), f x) ≤ ∑ i ∈ Finset.range N, a (i + k)) :
    (∫ x in Set.Ioi c, f x) ≤ ∑' n, a (n + k) :=
  le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Ioi c hInt
      (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop))
    ((summable_nat_add_iff k).mpr hsum).hasSum.tendsto_sum_nat hcmp

/-- Reverse-direction companion of `Real.integral_Ioi_le_tsum_of_window`: pass a finite-window
comparison `∑_{i<N} a(i+k) ≤ ∫_{c}^{c+N} f` to `∑' n, a(n+k) ≤ ∫_{Ioi c} f`. -/
theorem Real.tsum_le_integral_Ioi_of_window {a : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hsum : Summable a) (hInt : IntegrableOn f (Set.Ioi c))
    (hcmp : ∀ N : ℕ, ∑ i ∈ Finset.range N, a (i + k) ≤ ∫ x in c..(c + (N : ℝ)), f x) :
    ∑' n, a (n + k) ≤ ∫ x in Set.Ioi c, f x :=
  le_of_tendsto_of_tendsto'
    ((summable_nat_add_iff k).mpr hsum).hasSum.tendsto_sum_nat
    (intervalIntegral_tendsto_integral_Ioi c hInt
      (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop)) hcmp

/-- **Shifted tail `p`-series vs. improper integral.** For `m : ℕ`, `m > 0` and `a > 1`,
`∑_n (n+m+1)^{-a} ≤ ∫_m^∞ x^{-a} dx = m^{1-a}/(a-1)`. -/
theorem Real.tsum_one_div_nat_add_rpow_le {a : ℝ} (m : ℕ) (hm : 0 < m) (ha : 1 < a) :
    ∑' n : ℕ, 1 / ((n : ℝ) + (m + 1)) ^ a ≤ (m : ℝ) ^ (1 - a) / (a - 1) := by
  have hneg : (-a : ℝ) < -1 := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + (m + 1)) ^ a) :=
    ((summable_nat_add_iff (m + 1)).mpr (Real.summable_nat_rpow.mpr hneg)).congr fun n ↦ by
      push_cast; rw [Real.rpow_neg (by positivity), one_div]
  have hcmp : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + (m + 1)) ^ a
      ≤ ∫ x in (m : ℝ)..((m : ℝ) + (N : ℝ)), x ^ (-a) := fun N ↦ by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
      (Real.antitoneOn_rpow_neg_Icc (by linarith : (0 : ℝ) ≤ a) hm0).sum_le_integral
    rw [show (m : ℝ) + ((i + 1 : ℕ) : ℝ) = (i : ℝ) + (m + 1) by push_cast; ring,
      Real.rpow_neg (by positivity), one_div]
  have hintval : ∫ x in Set.Ioi (m : ℝ), x ^ (-a) = (m : ℝ) ^ (1 - a) / (a - 1) := by
    rw [integral_Ioi_rpow_of_lt hneg hm0, show (-a + 1 : ℝ) = 1 - a by ring,
      div_eq_div_iff (ne_of_lt (by linarith : (1 - a : ℝ) < 0))
        (ne_of_gt (by linarith : (0 : ℝ) < a - 1))]
    ring
  rw [← hintval]
  exact Real.tsum_le_integral_Ioi_of_window 0 hsum (integrableOn_Ioi_rpow_of_lt hneg hm0) hcmp

/-- **Shifted tail `p`-series bound.** For `a > 1`, `∑_n 1/(n+2)^a ≤ 1/(a-1)`, the `p`-series
form of the pole bound `ζ(a) - 1 ≤ 1/(a-1)`. -/
theorem Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one {a : ℝ} (ha : 1 < a) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a ≤ 1 / (a - 1) := by
  simpa [Real.one_rpow, one_add_one_eq_two] using Real.tsum_one_div_nat_add_rpow_le 1 one_pos ha

/-- The real tail `∑_n ((n+2)^{-σ})` of `ζ(σ) - 1` tends to `0` as `σ → +∞`. -/
private theorem tendsto_tsum_one_div_nat_add_two_rpow_atTop :
    Tendsto (fun σ : ℝ ↦ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ) atTop (𝓝 0) := by
  have hab : ∀ k : ℕ, Tendsto (fun σ : ℝ ↦ 1 / ((k : ℝ) + 2) ^ σ) atTop (𝓝 0) := by
    intro k
    have hb0 : -1 < ((k : ℝ) + 2)⁻¹ := by
      have : (0 : ℝ) < ((k : ℝ) + 2)⁻¹ := by positivity
      linarith
    have hb1 : ((k : ℝ) + 2)⁻¹ < 1 := by
      rw [inv_lt_one₀ (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    refine (tendsto_rpow_atTop_of_base_lt_one _ hb0 hb1).congr (fun σ ↦ ?_)
    rw [Real.inv_rpow (by positivity), one_div]
  have h_bound : ∀ᶠ σ : ℝ in atTop,
      ∀ k : ℕ, ‖1 / ((k : ℝ) + 2) ^ σ‖ ≤ 1 / ((k : ℝ) + 2) ^ (2 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ k
    rw [Real.norm_of_nonneg (by positivity)]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) hσ
  have := tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ ↦ (0 : ℝ))
    (Real.summable_one_div_nat_add_two_rpow (by norm_num)) hab h_bound
  simpa using this

/-- Termwise bound `‖ζ(s) - 1‖ ≤ ∑_n ((n+2)^{-Re s})`, for `Re s > 1`. -/
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re := by
  have hshift : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    refine h.congr (fun n ↦ ?_)
    push_cast; ring_nf
  have htn : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖ = 1 / ((n : ℝ) + 2) ^ s.re := by
    intro n
    rw [norm_div, norm_one]
    congr 1
    rw [show ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      norm_natCast_cpow_of_pos (by positivity)]
    push_cast; ring
  have hz : riemannZeta s - 1 = ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
    have key : riemannZeta s = 1 + ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hshift.tsum_eq_zero_add]
      congr 1
      · simp
      · refine tsum_congr (fun n ↦ ?_); push_cast; ring_nf
    rw [key]; ring
  rw [hz]
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖ :=
        norm_tsum_le_tsum_norm
          ((Real.summable_one_div_nat_add_two_rpow hs).congr (fun n ↦ (htn n).symm))
    _ = ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re := tsum_congr htn

/-- **`ζ(σ + it) → 1` as `σ → +∞`.** -/
theorem tendsto_riemannZeta_atTop_nhds_one (t : ℝ) :
    Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t)) atTop (𝓝 1) := by
  have h : Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_tsum_one_div_nat_add_two_rpow_atTop
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
    have hb := norm_riemannZeta_sub_one_le (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; exact hσ)
    rwa [hre] at hb
  have h1 := h.add_const (1 : ℂ)
  simpa using h1

/-- **`arg ζ(σ + it) → 0` as `σ → +∞`** (`lem:lb_arg_tendsto`). -/
theorem tendsto_arg_riemannZeta_atTop (t : ℝ) :
    Tendsto (fun σ : ℝ ↦ (riemannZeta ((σ : ℂ) + Complex.I * t)).arg) atTop (𝓝 0) := by
  have hcont : ContinuousAt Complex.arg 1 :=
    Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff])
  have := hcont.tendsto.comp (tendsto_riemannZeta_atTop_nhds_one t)
  simpa [Function.comp_def] using this

/-- The Basel-type value `∑_n ((n+2)^{-2}) = π²/6 - 1`. -/
private theorem tsum_one_div_nat_add_two_sq :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have key := Summable.sum_add_tsum_nat_add 2 hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at key
  norm_num at key
  simp only [one_div]
  linarith [key]

/-- Tail comparison across exponents: for `1 < a ≤ σ` the shifted `p`-series tail at `σ` is
bounded by the tail at `a` scaled by `2^{a-σ}`. -/
theorem Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum {a σ : ℝ} (ha : 1 < a) (hσ : a ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (2 : ℝ) ^ (a - σ) * ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a := by
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n ↦ ?_)
    (Real.summable_one_div_nat_add_two_rpow (ha.trans_le hσ))
    ((Real.summable_one_div_nat_add_two_rpow ha).mul_left _)
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hx : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [show (1 : ℝ) / ((n : ℝ) + 2) ^ σ = ((n : ℝ) + 2) ^ (-σ) by
        rw [Real.rpow_neg hxpos.le, one_div],
    show (2 : ℝ) ^ (a - σ) * (1 / ((n : ℝ) + 2) ^ a)
        = ((n : ℝ) + 2) ^ (-a) * (2 : ℝ) ^ (-(σ - a)) by
      rw [Real.rpow_neg hxpos.le, one_div, show a - σ = -(σ - a) by ring]; ring,
    show (-σ) = (-a) + (-(σ - a)) by ring, Real.rpow_add hxpos]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)) (Real.rpow_nonneg hxpos.le _)

/-- Exponential form of `Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum`: for `1 < a ≤ σ` the
shifted `p`-series tail at `σ` is dominated by `C₀ · exp (-(log 2)·σ)` with
`C₀ = (∑_n (n+2)^{-a})·2^a`. -/
theorem Real.tsum_one_div_nat_add_two_rpow_le_mul_exp_neg {a σ : ℝ} (ha : 1 < a) (hσ : a ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ
      ≤ ((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a) * Real.exp (-(Real.log 2 * σ)) := by
  refine (Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum ha hσ).trans (le_of_eq ?_)
  rw [show a - σ = a + (-σ) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show (2 : ℝ) ^ (-σ) = Real.exp (-(Real.log 2 * σ)) by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; ring]
  ring

/-- Tail estimate: for `σ ≥ 2` the real tail `∑_n ((n+2)^{-σ})` is `≤ (π²/6 - 1)·2^{2-σ}`. -/
private theorem tsum_one_div_nat_add_two_rpow_le_mul_rpow {σ : ℝ} (hσ : 2 ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - σ) := by
  have h := Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum (by norm_num : (1 : ℝ) < 2) hσ
  rw [tsum_congr fun n : ℕ ↦ show 1 / ((n : ℝ) + 2) ^ (2 : ℝ) = 1 / ((n : ℝ) + 2) ^ 2 by
        rw [← Real.rpow_natCast]; norm_num,
    tsum_one_div_nat_add_two_sq, mul_comm] at h
  exact h

/-- **Uniform tail bound for `Re s ≥ 2`.** -/
theorem norm_riemannZeta_sub_one_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have h1 : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re :=
    norm_riemannZeta_sub_one_le (by linarith)
  have h2 : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - s.re) :=
    tsum_one_div_nat_add_two_rpow_le_mul_rpow hs
  have h3 : (2 : ℝ) ^ (2 - s.re) ≤ 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : (0 : ℝ) ≤ Real.pi ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  calc ‖riemannZeta s - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - s.re) := h1.trans h2
    _ ≤ (Real.pi ^ 2 / 6 - 1) * 1 := mul_le_mul_of_nonneg_left h3 hpos
    _ = Real.pi ^ 2 / 6 - 1 := mul_one _

/-- **`ζ` stays in the slit plane for `Re s ≥ 2`**, so the principal argument may be read off
along any path with `Re ≥ 2`. -/
theorem riemannZeta_mem_slitPlane_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    riemannZeta s ∈ Complex.slitPlane := by
  have hb := norm_riemannZeta_sub_one_le_of_two_le_re hs
  have hlt : Real.pi ^ 2 / 6 - 1 < 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hre : -‖riemannZeta s - 1‖ ≤ (riemannZeta s - 1).re :=
    neg_le_of_abs_le (abs_re_le_norm (riemannZeta s - 1))
  rw [Complex.sub_re, Complex.one_re] at hre
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (by linarith)

/-- Near `1` the log-modulus is controlled by the displacement: if `‖w - 1‖ ≤ 1/2` then
`|log‖w‖| ≤ 2‖w - 1‖`. -/
private theorem abs_log_norm_le_two_mul_norm_sub_one {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    |Real.log ‖w‖| ≤ 2 * ‖w - 1‖ := by
  set ε : ℝ := ‖w - 1‖ with hε
  have htri : |‖w‖ - ‖(1 : ℂ)‖| ≤ ε := abs_norm_sub_norm_le w 1
  rw [norm_one, abs_le] at htri
  have hwlb : 1 - ε ≤ ‖w‖ := by linarith [htri.1]
  have hwub : ‖w‖ ≤ 1 + ε := by linarith [htri.2]
  have hwpos : 0 < ‖w‖ := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 := Real.one_sub_inv_le_log_of_pos hwpos
    have h1e : (0 : ℝ) < 1 - ε := by linarith
    have hinv1 := inv_anti₀ h1e hwlb
    have hle : (1 - ε)⁻¹ ≤ 1 + 2 * ε := by rw [inv_le_iff_one_le_mul₀ h1e]; nlinarith
    linarith
  · have h2 := Real.log_le_sub_one_of_pos hwpos
    linarith

/-- **Tail domination of the `I(t)` integrand.** For `σ ≥ 4` and any real `t`, the integrand
`log‖ζ(σ + it)‖` is dominated in absolute value by the integrable exponential
`8(π²/6 - 1)·exp(-(log 2)·σ)`. -/
theorem abs_log_norm_riemannZeta_le_exp {t σ : ℝ} (hσ : 4 ≤ σ) :
    |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖|
      ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  set w : ℂ := riemannZeta ((σ : ℂ) + Complex.I * t)
  have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
  have hb : ‖w - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have hb0 := norm_riemannZeta_sub_one_le (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith)
    rwa [hre] at hb0
  have htl : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - σ) :=
    tsum_one_div_nat_add_two_rpow_le_mul_rpow (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hconv : (2 : ℝ) ^ (2 - σ) = 4 * Real.exp (-(Real.log 2 * σ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      show Real.log 2 * (2 - σ) = Real.log 2 * 2 + -(Real.log 2 * σ) by ring, Real.exp_add,
      show Real.log 2 * 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; ring,
      Real.exp_log (by norm_num)]
    norm_num
  have hbound : ‖w - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ))) := by
    rw [← hconv]; exact hb.trans htl
  have hsmall : ‖w - 1‖ ≤ 1 / 2 := by
    have hexple : Real.exp (-(Real.log 2 * σ)) ≤ Real.exp (-(Real.log 2 * 4)) := by
      apply Real.exp_le_exp.mpr; nlinarith [hl2]
    have hSle : Real.pi ^ 2 / 6 - 1 ≤ 2 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have he4 : (4 : ℝ) * Real.exp (-(Real.log 2 * 4)) ≤ 1 / 4 := by
      have he : Real.exp (-(Real.log 2 * 4)) = (2 : ℝ) ^ (-(4 : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
      rw [he, Real.rpow_neg (by norm_num),
        show (2 : ℝ) ^ (4 : ℝ) = 16 by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      norm_num
    calc ‖w - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ))) := hbound
      _ ≤ 2 * (4 * Real.exp (-(Real.log 2 * 4))) := by
            apply mul_le_mul hSle ?_ (by positivity) (by norm_num)
            exact mul_le_mul_of_nonneg_left hexple (by norm_num)
      _ ≤ 2 * (1 / 4) := by linarith [he4]
      _ ≤ 1 / 2 := by norm_num
  calc |Real.log ‖w‖| ≤ 2 * ‖w - 1‖ := abs_log_norm_le_two_mul_norm_sub_one hsmall
    _ ≤ 2 * ((Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ)))) := by linarith [hbound]
    _ = 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by ring

/-- The exponential `σ ↦ exp(-(b·σ))` (with `b > 0`) is integrable on every right-infinite ray
`(c, ∞)`. The `neg_mul`-normalised restatement of mathlib's `exp_neg_integrableOn_Ioi`. -/
theorem Real.integrableOn_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ Real.exp (-(b * σ))) (Set.Ioi c) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi c hb

/-- **Continuity of the `I(t)` integrand.** On any set `S` of abscissae along which the path
`σ ↦ σ + it` avoids the pole `1` and the zeros of `ζ`, the integrand `σ ↦ log‖ζ(σ + it)‖` is
continuous. -/
theorem continuousOn_log_norm_riemannZeta {t : ℝ} {S : Set ℝ}
    (hpole : ∀ σ ∈ S, ((σ : ℂ) + Complex.I * t) ≠ 1)
    (hzero : ∀ σ ∈ S, riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    ContinuousOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S := by
  have hpath : Continuous fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) :=
    Complex.continuous_ofReal.add continuous_const
  have hcontζ : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t)) S := by
    have hc : ContinuousOn riemannZeta {s : ℂ | s ≠ 1} :=
      fun s hs ↦ (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt
    exact hc.comp hpath.continuousOn hpole
  refine Real.continuousOn_log.comp hcontζ.norm (fun σ hσ ↦ ?_)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, norm_ne_zero_iff]
  exact hzero σ hσ

/-- **Convergence of `I`** (`lem:lb_I_integrable`). For `t ≠ 0` with no zero of `ζ` on the closed
ray `{σ + it : σ ≥ 1/2}`, the integrand of `I(t)` is integrable on `[1/2, ∞)`, so
`logNormZetaIntegral t` is well defined and finite. -/
theorem integrableOn_log_norm_riemannZeta_Ioi {t : ℝ} (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ioi (1 / 2 : ℝ)) := by
  set f : ℝ → ℝ := fun σ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ with hf
  have hne1 : ∀ σ : ℝ, ((σ : ℂ) + Complex.I * t) ≠ 1 := by
    intro σ h
    have him : ((σ : ℂ) + Complex.I * t).im = t := by simp
    rw [h] at him; simp only [one_im] at him; exact ht him.symm
  have hfcont : ContinuousOn f (Set.Ici (1 / 2 : ℝ)) :=
    continuousOn_log_norm_riemannZeta (fun σ _ ↦ hne1 σ) (fun σ hσ ↦ hne σ hσ)
  -- Split at `σ = 4`, the smallest convenient cut making the tail bound
  -- `‖ζ(σ + it) - 1‖ ≤ (π²/6 - 1)·2^{2-σ}` drop below `1/2` on `(4, ∞)`.
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 4 by norm_num)]
  apply IntegrableOn.union
  · exact (ContinuousOn.integrableOn_Icc
      (hfcont.mono Set.Icc_subset_Ici_self)).mono_set Set.Ioc_subset_Icc_self
  · have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hmaj : IntegrableOn
        (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
        (Set.Ioi (4 : ℝ)) := (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · refine (hfcont.mono ?_).aestronglyMeasurable measurableSet_Ioi
      intro x hx
      exact le_of_lt (lt_trans (by norm_num) (Set.mem_Ioi.mp hx))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      have hσ4 : (4 : ℝ) < σ := Set.mem_Ioi.mp hσ
      rw [Real.norm_eq_abs, hf]
      exact abs_log_norm_riemannZeta_le_exp hσ4.le

/-- The prime-indexed summand `p ↦ p^{-s}` is summable for `Re s > 1`. -/
private theorem summable_prime_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ (p : ℂ) ^ (-s)) := by
  have h : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    refine (Complex.summable_one_div_nat_cpow.mpr hs).congr (fun n ↦ ?_)
    rw [Complex.cpow_neg, one_div]
  exact h.comp_injective Nat.Primes.coe_nat_injective

/-- **Euler-product lower bound on `log‖ζ‖`.** For `σ > 1` and any `t`, `log‖ζ(σ + it)‖` is
bounded below by minus the real `p`-series tail `∑_n (n+2)^{-σ} = ζ(σ) - 1`. -/
theorem neg_tsum_one_div_le_log_norm_riemannZeta {σ t : ℝ} (hσ : 1 < σ) :
    -(∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ)
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hs1 : 1 < s.re := hsre ▸ hσ
  have hsummand := summable_prime_cpow_neg hs1
  have hlog : Summable (fun p : Nat.Primes ↦ -Complex.log (1 - (p : ℂ) ^ (-s))) :=
    (hsummand.clog_one_sub).neg
  have hre : Summable (fun p : Nat.Primes ↦ (-Complex.log (1 - (p : ℂ) ^ (-s))).re) :=
    (Complex.hasSum_re hlog.hasSum).summable
  -- the identity `log‖ζ s‖ = ∑_p Re(-log(1 - p^{-s}))`
  have hlogeq : Real.log ‖riemannZeta s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
    have hnorm : ‖riemannZeta s‖
        = Real.exp ((∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))).re) := by
      rw [← riemannZeta_eulerProduct_exp_log hs1, Complex.norm_exp]
    rw [hnorm, Real.log_exp, Complex.re_tsum hlog]
  -- the termwise lower bound `-(1/p^σ) ≤ Re(-log(1 - p^{-s}))`
  have hterm : ∀ p : Nat.Primes,
      -(1 / (p : ℝ) ^ σ) ≤ (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    have hppos : (0 : ℝ) < (p : ℝ) := by positivity
    have hnormcp : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-σ) := by
      rw [norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hsre]
    have hlt1 : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hxne1 : (p : ℂ) ^ (-s) ≠ 1 := by
      intro h; rw [h, norm_one] at hnormcp; linarith
    have hwpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxne1))
    have hwle : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-σ) := by
      calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ = 1 + (p : ℝ) ^ (-σ) := by rw [norm_one, hnormcp]
    rw [Complex.neg_re, Complex.log_re, neg_le_neg_iff]
    calc Real.log ‖1 - (p : ℂ) ^ (-s)‖
        ≤ Real.log (1 + (p : ℝ) ^ (-σ)) := Real.log_le_log hwpos hwle
      _ ≤ (p : ℝ) ^ (-σ) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) by linarith)
          linarith
      _ = 1 / (p : ℝ) ^ σ := by rw [Real.rpow_neg hppos.le, one_div]
  -- compare the prime tail with the full `(n+2)` tail
  have hsum_tail : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ σ) :=
    Real.summable_one_div_nat_add_two_rpow hσ
  have hsum_prime : Summable (fun p : Nat.Primes ↦ 1 / (p : ℝ) ^ σ) :=
    (Real.summable_one_div_nat_rpow.mpr hσ).comp_injective Nat.Primes.coe_nat_injective
  have hcmp3 : ∑' p : Nat.Primes, 1 / (p : ℝ) ^ σ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have hi : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ) - 2) := by
      intro p q h
      have hp := p.2.two_le
      have hq := q.2.two_le
      simp only at h
      exact Subtype.ext (by lia)
    have h := tsum_comp_le_tsum_of_inj hsum_tail (fun n ↦ by positivity) hi
    refine le_trans (le_of_eq ?_) h
    refine tsum_congr (fun p ↦ ?_)
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hcast : (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = (p : ℝ) := by
      rw [Nat.cast_sub hp2]; push_cast; ring
    simp only [Function.comp_apply, hcast]
  rw [hlogeq]
  calc -(∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ)
      ≤ -(∑' p : Nat.Primes, 1 / (p : ℝ) ^ σ) := neg_le_neg hcmp3
    _ = ∑' p : Nat.Primes, -(1 / (p : ℝ) ^ σ) := by rw [tsum_neg]
    _ ≤ ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re :=
        Summable.tsum_le_tsum hterm hsum_prime.neg hre

/-- **Upper bound on `log‖ζ‖`.** For `σ > 1`, `log‖ζ(σ + it)‖ ≤ ∑_n (n+2)^{-σ} = ζ(σ) - 1`. -/
theorem log_norm_riemannZeta_le_tsum_one_div {σ t : ℝ} (hσ : 1 < σ) :
    Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hs1 : 1 < s.re := hsre ▸ hσ
  have htail := norm_riemannZeta_sub_one_le hs1
  rw [hsre] at htail
  have htnn : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := tsum_nonneg (fun n ↦ by positivity)
  have hnorm_le : ‖riemannZeta s‖ ≤ 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    calc ‖riemannZeta s‖ = ‖1 + (riemannZeta s - 1)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ)‖ + ‖riemannZeta s - 1‖ := norm_add_le _ _
      _ ≤ 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by rw [norm_one]; linarith
  have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hs1.le)
  calc Real.log ‖riemannZeta s‖
      ≤ Real.log (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ) := Real.log_le_log hpos hnorm_le
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
        have := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ by linarith)
        linarith

/-- **Two-sided bound on `log‖ζ‖`.** For `σ > 1`, `|log‖ζ(σ + it)‖| ≤ ∑_n (n+2)^{-σ}`. -/
theorem abs_log_norm_riemannZeta_le_tsum_one_div {σ t : ℝ} (hσ : 1 < σ) :
    |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ :=
  abs_le.mpr ⟨neg_tsum_one_div_le_log_norm_riemannZeta hσ,
    log_norm_riemannZeta_le_tsum_one_div hσ⟩

/-- Given a nonnegative integrable majorant `g` on `(a, ∞)` with
`∫_a^∞ g ≤ C` and `-g ≤ log‖ζ(σ+it)‖` pointwise, both `∫_a^∞ log‖ζ‖` and, for any upper limit `b`,
`∫_a^b log‖ζ‖` are `≥ -C`. -/
theorem neg_le_logNormZetaIntegral_of_majorant {a C b t : ℝ} {g : ℝ → ℝ}
    (hg_int : IntegrableOn g (Set.Ioi a)) (hgnn : ∀ σ ∈ Set.Ioi a, 0 ≤ g σ)
    (hgC : ∫ σ in Set.Ioi a, g σ ≤ C)
    (hle : ∀ σ ∈ Set.Ioi a, -g σ ≤ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
    (hlog_int : IntegrableOn
      (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) (Set.Ioi a)) :
    (-C ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-C ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioi a := fun x hx ↦ hx.1
  have hmono := setIntegral_mono_on hg_int.neg hlog_int measurableSet_Ioi hle
  have hmono' := setIntegral_mono_on (hg_int.mono_set hsub).neg (hlog_int.mono_set hsub)
    measurableSet_Ioo (fun σ hσ ↦ hle σ (hsub hσ))
  simp only [Pi.neg_apply, integral_neg] at hmono hmono'
  have hgle : ∫ σ in Set.Ioo a b, g σ ≤ C := by
    refine le_trans (setIntegral_mono_set hg_int ?_ hsub.eventuallyLE) hgC
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ using hgnn σ hσ
  exact ⟨by linarith, by linarith⟩

/-- `log‖ζ(σ+it)‖` is integrable on `(a, ∞)` for `a > 1`. -/
theorem integrableOn_log_norm_riemannZeta_Ioi_of_one_lt {a : ℝ} (ha : 1 < a) (t : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ioi a) := by
  have hre : ∀ σ : ℝ, ((σ : ℂ) + Complex.I * t).re = σ := fun σ ↦ by simp
  have hcontlog := continuousOn_log_norm_riemannZeta (S := Set.Ioi a)
    (fun σ hσ h ↦ by
      have hσ1 : 1 < σ := lt_trans ha hσ
      have h1 := hre σ
      rw [h, Complex.one_re] at h1
      linarith)
    (fun σ hσ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact (lt_trans ha hσ).le))
  refine Integrable.mono' ((Real.integrableOn_exp_neg_mul_Ioi (Real.log_pos one_lt_two) a).const_mul
      ((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a))
    (hcontlog.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [Real.norm_eq_abs]
  exact (abs_log_norm_riemannZeta_le_tsum_one_div (lt_trans ha hσ)).trans
    (Real.tsum_one_div_nat_add_two_rpow_le_mul_exp_neg ha hσ.le)

/-- **Tail witness from any majorant of the `ζ`-tail sum.** For `1 < a`, let `g` be integrable on
`(a, ∞)` with `∑_n (n+2)^{-σ} ≤ g σ` there and `∫_a^∞ g ≤ C`. Then both `∫_a^∞ log‖ζ(σ+it)‖` and,
for any upper limit `b`, `∫_a^b log‖ζ(σ+it)‖` are `≥ -C`. -/
theorem neg_le_logNormZetaIntegral_of_tsum_le {a C b t : ℝ} {g : ℝ → ℝ} (ha : 1 < a)
    (hg_int : IntegrableOn g (Set.Ioi a))
    (hg : ∀ σ ∈ Set.Ioi a, ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ g σ)
    (hgC : ∫ σ in Set.Ioi a, g σ ≤ C) :
    (-C ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-C ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_majorant hg_int
    (fun σ hσ ↦ (tsum_nonneg fun n ↦ by positivity).trans (hg σ hσ)) hgC
    (fun σ hσ ↦ by
      linarith [hg σ hσ, neg_tsum_one_div_le_log_norm_riemannZeta (t := t) (lt_trans ha hσ)])
    (integrableOn_log_norm_riemannZeta_Ioi_of_one_lt ha t)

/-- **The tail witness with its constant exposed.** The geometric-majorant instance of
`neg_le_logNormZetaIntegral_of_tsum_le`, with `C_t = (∑_n 1/(n+2)^a)/log 2 = (ζ(a) - 1)/log 2`. -/
theorem logNormZetaIntegral_tail_ge_const {a : ℝ} (ha : 1 < a) (b t : ℝ) :
    (-((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) / Real.log 2)
        ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) / Real.log 2)
        ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine neg_le_logNormZetaIntegral_of_tsum_le
    (g := fun σ ↦ (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a * Real.exp (-(Real.log 2 * σ))) ha
    ((Real.integrableOn_exp_neg_mul_Ioi hl2 a).const_mul _)
    (fun σ hσ ↦ Real.tsum_one_div_nat_add_two_rpow_le_mul_exp_neg ha hσ.le) (le_of_eq ?_)
  have hexpint : ∫ σ in Set.Ioi a, Real.exp (-(Real.log 2 * σ))
      = Real.exp (-(Real.log 2 * a)) / Real.log 2 := by
    have h := integral_exp_mul_Ioi (a := -Real.log 2) (by linarith) a
    simp only [neg_mul] at h
    rw [h]; ring
  have h2a : (2 : ℝ) ^ a * Real.exp (-(Real.log 2 * a)) = 1 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add, add_neg_cancel,
      Real.exp_zero]
  rw [integral_const_mul, hexpint,
    show (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a
          * (Real.exp (-(Real.log 2 * a)) / Real.log 2)
        = (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * (2 ^ a * Real.exp (-(Real.log 2 * a)))
          / Real.log 2 by ring, h2a, mul_one]

/-- **Lower bound on the tail of `I(t)`** (`lem:ll_tail`). For a width-`d` strip with `d > 1/2`,
both `∫_{1/2+d}^∞ log|ζ(σ+it)| dσ` and `∫_{1/2+d}^{1/2+2d} log|ζ(σ+it)| dσ` are bounded below by a
single `t`-independent constant. -/
theorem logNormZetaIntegral_tail_ge {d : ℝ} (hd : 1 / 2 < d) :
    ∃ C : ℝ, ∀ t : ℝ,
      (-C ≤ ∫ σ in Set.Ioi (1 / 2 + d), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) ∧
      (-C ≤ ∫ σ in Set.Ioo (1 / 2 + d) (1 / 2 + 2 * d),
              Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  ⟨_, fun t ↦ logNormZetaIntegral_tail_ge_const (by linarith) (1 / 2 + 2 * d) t⟩

