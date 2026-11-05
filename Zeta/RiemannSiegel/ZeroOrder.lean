/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Analysis.Complex.Cpow
public import Zeta.Analysis.SpecialFunctions.Sqrt
public import Zeta.RiemannSiegel.Defs
public import Zeta.RiemannSiegel.Bound
public import Zeta.RiemannSiegel.Shift
public import Zeta.RiemannSiegel.Siegel
public import Zeta.Zeros.HardyZ

/-!
# The order-zero Riemann–Siegel formula

Hardy's `Z(t)` is evaluated to within `O(T^{-1/4})` by the **main sum**
`S(t, ν) = 2 ∑_{n ≤ ν} n^{-1/2} cos (θ(t) − t log n)` of `⌊√T⌋` terms, `T = t/2π`
(`riemann_siegel_zero.tex`, `cha:rs_zero`). This is the asymptotic gain over the `Θ(t)` terms per
point of the Euler–Maclaurin evaluation of `Zeta/Zeros/HardyZ.lean`.

The passage from the contour integral `I(s, a)` of `Zeta/RiemannSiegel/Integral.lean` to the main
sum is exact and unconditional: it is the contour-shift identity
`Zeta.RiemannSiegel.sum_cpow_neg_eq_contourIntegral_sub_contourIntegral` read through the phase
`e^{iθ(t)}`, and it is `mainSum_eq_two_re_exp_mul_contourIntegral_sub` below.

Identifying the remaining `ν`-independent term `2 Re (e^{iθ(t)} I(s, ½))` as `−Z(t)` is **Siegel's
identity** (`riemann_siegel_zero.tex`, `thm:rsz_siegel`), proved in
`Zeta/RiemannSiegel/Siegel.lean`. The whole chain is therefore unconditional.

## Main definitions

* `Zeta.RiemannSiegel.mainSum`: the main sum `S(t, ν)`;
* `Zeta.RiemannSiegel.mainSumOfPhase`: the same sum with the phase `θ` a parameter, which is what
  an implementation evaluates, at a Stirling approximant of `riemannSiegelTheta`.

## Main results

* `Zeta.RiemannSiegel.mainSum_eq_two_re_exp_mul_contourIntegral_sub`: the exact reduction
  `S(t, ν) = 2 Re (e^{iθ(t)} I(s, ν+½)) − 2 Re (e^{iθ(t)} I(s, ½))`;
* `Zeta.RiemannSiegel.hardyZ_eq_mainSum_sub`: the order-zero formula
  `Z(t) = S(t, ν) − 2 Re (e^{iθ(t)} I(s, ν+½))`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_two_mul_norm`: the error is at most
  `2 ‖I(s, ν+½)‖`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_hundredNinety`,
  `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_threeHundredTwo`: the resulting bounds
  `|Z(t) − S(t, ⌊√T⌋)| ≤ 190 T^{-1/4} ≤ 302 t^{-1/4}` for `t ≥ 32π`;
* `Zeta.RiemannSiegel.abs_mainSumOfPhase_sub_mainSumOfPhase_le`: the main sum is `4√ν`-Lipschitz
  in its phase, so a phase error is amplified by `4√ν` rather than carried through unchanged.
-/
@[expose] public section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/-- The **Riemann–Siegel main sum**
`S(t, ν) = 2 ∑_{n = 1}^{ν} n^{-1/2} cos (θ(t) − t log n)`. -/
noncomputable def mainSum (t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (riemannSiegelTheta t - t * Real.log n) / Real.sqrt n

/-- **The exact reduction of the main sum to the contour integral.** -/
theorem mainSum_eq_two_re_exp_mul_contourIntegral_sub (t : ℝ) (ν : ℕ) :
    mainSum t ν
      = 2 * (exp (I * riemannSiegelTheta t) *
          contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)).re
        - 2 * (exp (I * riemannSiegelTheta t) * contourIntegral (1 / 2 + t * I) (1 / 2)).re := by
  have hsum : (exp (I * (riemannSiegelTheta t : ℂ)) *
        ∑ n ∈ Finset.Icc 1 ν, (n : ℂ) ^ (-(1 / 2 + (t : ℂ) * I))).re
      = ∑ n ∈ Finset.Icc 1 ν, Real.cos (riemannSiegelTheta t - t * Real.log n) / Real.sqrt n := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    rw [← Complex.ofReal_natCast n]
    exact Complex.re_exp_mul_I_mul_cpow_neg hn0 t (riemannSiegelTheta t)
  rw [mainSum, ← hsum, sum_cpow_neg_eq_contourIntegral_sub_contourIntegral, mul_sub,
    Complex.sub_re]
  ring

/-- **The order-zero Riemann–Siegel formula** (`riemann_siegel_zero.tex`, `thm:rsz_formula`). -/
theorem hardyZ_eq_mainSum_sub {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    hardyZ t = mainSum t ν
      - 2 * (exp (I * riemannSiegelTheta t) *
          contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)).re := by
  set θ : ℝ := riemannSiegelTheta t with hθ
  set J : ℂ := contourIntegral (1 / 2 + t * I) (1 / 2)
  have hphase : exp (I * (θ : ℂ)) * (exp (-(2 * (θ : ℂ)) * I) * (starRingEnd ℂ) J)
      = (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J) := by
    rw [map_mul, ← Complex.exp_conj, ← mul_assoc, ← exp_add, map_mul, Complex.conj_I,
      Complex.conj_ofReal, show I * (θ : ℂ) + -(2 * (θ : ℂ)) * I = -I * (θ : ℂ) by ring]
  have hkey : hardyZ t = -(2 * (exp (I * (θ : ℂ)) * J).re) := by
    rw [hardyZ, ← hθ, show (1 / 2 + I * (t : ℂ)) = 1 / 2 + (t : ℂ) * I by ring,
      riemannZeta_eq_neg_contourIntegral_sub ht, mul_sub, mul_neg, hphase,
      show -(exp (I * (θ : ℂ)) * J) - (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J)
        = -(exp (I * (θ : ℂ)) * J + (starRingEnd ℂ) (exp (I * (θ : ℂ)) * J)) by ring,
      Complex.add_conj]
    simp
  rw [mainSum_eq_two_re_exp_mul_contourIntegral_sub, hkey]
  ring

/-- **The order-zero error is at most twice the modulus of the shifted contour integral.** -/
theorem abs_hardyZ_sub_mainSum_le_two_mul_norm {t : ℝ} (ht : 0 < t) (ν : ℕ) :
    |hardyZ t - mainSum t ν| ≤ 2 * ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)‖ := by
  rw [hardyZ_eq_mainSum_sub ht ν, sub_sub_cancel_left, abs_neg, abs_mul, abs_two]
  gcongr
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  rw [norm_mul, mul_comm I ((riemannSiegelTheta t : ℝ) : ℂ), Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The order-zero bound** (`riemann_siegel_zero.tex`, `cor:rsz_bound`), in terms of
`T = t/2π`. -/
theorem abs_hardyZ_sub_mainSum_le_hundredNinety {t : ℝ} (ht : 32 * π ≤ t) :
    |hardyZ t - mainSum t ⌊Real.sqrt (t / (2 * π))⌋₊|
      ≤ 190 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set ν : ℕ := ⌊Real.sqrt (t / (2 * π))⌋₊
  have hbound : ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)‖
      ≤ 95 * (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
    refine norm_contourIntegral_le_ninetyFive ht (n := (ν : ℤ)) (by push_cast; ring) ?_ ?_
    · exact_mod_cast Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))
    · exact_mod_cast Nat.lt_floor_add_one (Real.sqrt (t / (2 * π)))
  linarith [abs_hardyZ_sub_mainSum_le_two_mul_norm ht0 ν]

/-- **The order-zero bound in terms of `t`** rather than of `T = t/2π`. -/
theorem abs_hardyZ_sub_mainSum_le_threeHundredTwo {t : ℝ} (ht : 32 * π ≤ t) :
    |hardyZ t - mainSum t ⌊Real.sqrt (t / (2 * π))⌋₊| ≤ 302 * t ^ (-(1 / 4) : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set ν : ℕ := ⌊Real.sqrt (t / (2 * π))⌋₊
  have hbound : ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)‖
      ≤ 151 * t ^ (-(1 / 4) : ℝ) := by
    refine norm_contourIntegral_le_hundredFiftyOne ht (n := (ν : ℤ)) (by push_cast; ring) ?_ ?_
    · exact_mod_cast Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))
    · exact_mod_cast Nat.lt_floor_add_one (Real.sqrt (t / (2 * π)))
  linarith [abs_hardyZ_sub_mainSum_le_two_mul_norm ht0 ν]

/-! ### The main sum at an approximate phase

`mainSum` carries the exact `riemannSiegelTheta`, which no implementation evaluates exactly. The
phase is therefore made a parameter, and the resulting sum is Lipschitz in it.
-/

/-- `mainSum` is `mainSumOfPhase` at the exact phase. -/
theorem mainSum_eq_mainSumOfPhase (t : ℝ) (ν : ℕ) :
    mainSum t ν = mainSumOfPhase (riemannSiegelTheta t) t ν := rfl

/-- **The main sum is `4√ν`-Lipschitz in its phase.** -/
theorem abs_mainSumOfPhase_sub_mainSumOfPhase_le (θ₁ θ₂ t : ℝ) (ν : ℕ) :
    |mainSumOfPhase θ₁ t ν - mainSumOfPhase θ₂ t ν| ≤ 4 * Real.sqrt ν * |θ₁ - θ₂| := by
  have hterm : ∀ n ∈ Finset.Icc 1 ν,
      |Real.cos (θ₁ - t * Real.log n) / Real.sqrt n
        - Real.cos (θ₂ - t * Real.log n) / Real.sqrt n| ≤ |θ₁ - θ₂| * (1 / Real.sqrt n) := by
    intro n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (Finset.mem_Icc.1 hn).1)
    rw [div_sub_div_same, abs_div, abs_of_pos hs, mul_one_div]
    gcongr ?_ / _
    simpa using Real.abs_cos_sub_cos_le (θ₁ - t * Real.log n) (θ₂ - t * Real.log n)
  calc |mainSumOfPhase θ₁ t ν - mainSumOfPhase θ₂ t ν|
      = 2 * |∑ n ∈ Finset.Icc 1 ν, (Real.cos (θ₁ - t * Real.log n) / Real.sqrt n
              - Real.cos (θ₂ - t * Real.log n) / Real.sqrt n)| := by
        rw [mainSumOfPhase, mainSumOfPhase, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_two]
    _ ≤ 2 * ∑ n ∈ Finset.Icc 1 ν, |θ₁ - θ₂| * (1 / Real.sqrt n) := by
        gcongr; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * (|θ₁ - θ₂| * ∑ n ∈ Finset.Icc 1 ν, 1 / Real.sqrt n) := by rw [← Finset.mul_sum]
    _ ≤ 2 * (|θ₁ - θ₂| * (2 * Real.sqrt ν)) := by gcongr; exact Real.sum_one_div_sqrt_le ν
    _ = 4 * Real.sqrt ν * |θ₁ - θ₂| := by ring

end Zeta.RiemannSiegel
