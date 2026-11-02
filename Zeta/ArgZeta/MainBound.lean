/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.Littlewood
public import Zeta.ArgZeta.UpperBound
public import Zeta.ArgZeta.LowerBound

/-!
# Lehman's bound on `∫ S(t) dt`

**Lehman's bound** `|∫_{t₁}^{t₂} S(t) dt| ≤ A + B log(t₂/2π)` with `B = 0.128`
(`thm:lb_main`), assembled from Littlewood's reduction and the upper and lower bounds on
`logNormZetaIntegral`.

## Main results

- `norm_integral_argZeta_le_of_bounds'`, `norm_integral_argZeta_le_of_bounds`: parametric cores,
  taking explicit constants for the two `I(t)` bounds and returning an explicit `A`.
- `norm_integral_argZeta_le` (`thm:lb_main`): Lehman's bound with `A` existential.
- `norm_integral_argZeta_le_explicit`: the concrete `A = 13`, under a remaining numerical
  hypothesis `a₂ ≤ 30` on the additive constant of the lower `I(t)` bound.
-/
@[expose] public section


open Complex Filter Topology MeasureTheory Set

open scoped Real


/-- **Fully parametric core of Lehman's bound.** Lehman's bound with explicit
`A = ((a₁+a₂) + (b₁+b₂) log 2π)/π`, for any admissible pair of leading coefficients `b₁, b₂`
in the two `I(t)` bounds. -/
theorem norm_integral_argZeta_le_of_bounds' {a₁ a₂ b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb : b₁ + b₂ ≤ 0.128 * Real.pi)
    (ha₁ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      logNormZetaIntegral t ≤ a₁ + b₁ * Real.log t)
    (ha₂ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + b₂ * Real.log t) :
    ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t|
        ≤ ((a₁ + a₂) + (b₁ + b₂) * Real.log (2 * Real.pi)) / Real.pi
          + 0.128 * Real.log (t₂ / (2 * Real.pi)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  intro t₁ t₂ ht1 h12 hne1 hne2
  have ht1pos : 0 < t₁ := lt_trans (by positivity) ht1
  have ht2' : 168 * Real.pi ≤ t₂ := ht1.le.trans h12.le
  -- `log t₂` splits across `t₂/2π`, with a non-negative quotient part
  have hlogeq : Real.log t₂ = Real.log (t₂ / (2 * Real.pi)) + Real.log (2 * Real.pi) := by
    rw [Real.log_div (ht1pos.trans h12).ne' (by positivity)]; ring
  have hLpos : 0 ≤ Real.log (t₂ / (2 * Real.pi)) :=
    Real.log_nonneg <| (one_le_div (by positivity)).2 <| by nlinarith
  -- push `log t₁ ≤ log t₂` through the two non-negative leading coefficients
  have hlogmono := Real.log_le_log ht1pos h12.le
  have hm₁ := mul_le_mul_of_nonneg_left hlogmono hb₁
  have hm₂ := mul_le_mul_of_nonneg_left hlogmono hb₂
  have hmul := mul_le_mul_of_nonneg_right hb hLpos
  -- transfer to `|∫ S|` via Littlewood's `π ∫ S = I(t₂) - I(t₁)`
  have e1 : Real.pi * |∫ t in t₁..t₂, argZeta t|
      = |logNormZetaIntegral t₂ - logNormZetaIntegral t₁| := by
    rw [← pi_mul_integral_argZeta_eq_sub h12 ht1pos hne1 hne2, abs_mul, abs_of_pos hπ]
  refine le_of_mul_le_mul_left ?_ hπ
  rw [e1, mul_add, mul_div_cancel₀ _ hπ.ne', abs_le]
  constructor <;>
    nlinarith [ha₁ t₁ ht1.le hne1, ha₁ t₂ ht2' hne2, ha₂ t₁ ht1.le hne1, ha₂ t₂ ht2' hne2]

/-- **Parametric core of Lehman's bound.** The `d = 53/100`, `c = 5/2` specialisation of
`norm_integral_argZeta_le_of_bounds'`, with explicit
`A = ((a₁+a₂) + (3/16 + (3/4)(53/100)²) log 2π)/π`. -/
theorem norm_integral_argZeta_le_of_bounds {a₁ a₂ : ℝ}
    (ha₁ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      logNormZetaIntegral t ≤ a₁ + 3 / 16 * Real.log t)
    (ha₂ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ a₂ + 3 / 4 * (53 / 100) ^ 2 * Real.log t) :
    ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t|
        ≤ ((a₁ + a₂) + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * Real.pi)) / Real.pi
          + 0.128 * Real.log (t₂ / (2 * Real.pi)) :=
  norm_integral_argZeta_le_of_bounds' (by norm_num) (by positivity)
    (by nlinarith [Real.pi_gt_d2]) ha₁ ha₂

/-- **Lehman's bound** (`thm:lb_main`). `|∫_{t₁}^{t₂} S(t) dt| ≤ A + 0.128 · log(t₂/2π)` for
some constant `A`, where `S = argZeta`, provided `t₁, t₂` are not ordinates of zeros of `ζ` in
the half-plane `Re s ≥ 1/2`. -/
theorem norm_integral_argZeta_le :
    ∃ A : ℝ, ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ A + 0.128 * Real.log (t₂ / (2 * Real.pi)) := by
  obtain ⟨a₁, ha₁⟩ := logNormZetaIntegral_le
  obtain ⟨a₂, ha₂⟩ := le_logNormZetaIntegral (d := 53 / 100) (by norm_num) (by norm_num)
  exact ⟨_, norm_integral_argZeta_le_of_bounds ha₁ ha₂⟩

/-- **Weak, explicit-`A` form of Lehman's bound.** `|∫_{t₁}^{t₂} S(t) dt| ≤ 13 + 0.128 ·
log(t₂/2π)`, under a remaining numerical hypothesis `a₂ ≤ 30` on the additive constant of the
lower `I(t)` bound. -/
theorem norm_integral_argZeta_le_explicit
    (ha₂ : ∀ t : ℝ, 168 * Real.pi ≤ t →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t) ≠ 0) →
      -logNormZetaIntegral t ≤ 30 + 3 / 4 * (53 / 100) ^ 2 * Real.log t) :
    ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₁) ≠ 0) →
      (∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + I * t₂) ≠ 0) →
      |∫ t in t₁..t₂, argZeta t| ≤ 13 + 0.128 * Real.log (t₂ / (2 * Real.pi)) := by
  intro t₁ t₂ ht1 h12 hne1 hne2
  refine (norm_integral_argZeta_le_of_bounds
    (fun _ ht hzero ↦ logNormZetaIntegral_le_nine ht hzero) ha₂ t₁ t₂ ht1 h12 hne1 hne2).trans ?_
  -- `((9 + 30) + coeff · log 2π)/π ≤ 13`, leaving the common `0.128 · log(t₂/2π)` term
  -- (`log 2π = log 2 + log π ≤ 0.694 + (π - 1)`, and `π > 3.1415`)
  have hconst :
      (9 + 30 + (3 / 16 + 3 / 4 * (53 / 100) ^ 2) * Real.log (2 * Real.pi)) / Real.pi ≤ 13 := by
    rw [Real.log_mul two_ne_zero Real.pi_pos.ne', div_le_iff₀ Real.pi_pos]
    linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_gt_d4,
      Real.pi_lt_d4]
  linarith [hconst]

