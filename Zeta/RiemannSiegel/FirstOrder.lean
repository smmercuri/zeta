/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.RiemannSiegel.Correction
public import Zeta.RiemannSiegel.Linear
public import Zeta.RiemannSiegel.LinearTail
public import Zeta.RiemannSiegel.Outer
public import Zeta.RiemannSiegel.OuterSharp
public import Zeta.RiemannSiegel.Theta
public import Zeta.RiemannSiegel.ZeroOrder

/-!
# The first-order Riemann–Siegel formula

The capstones of `riemann_siegel_first.tex`, `cha:rs_first`.

`sec:rsf_saddle`: the Riemann–Siegel contour integral `I(½ + it, ν + ½)` agrees, to within
`22 T^{-3/4}` with `T = t/2π`, with the saddle factor `(-1)^ν T^{-1/4} e^{-i(ϑ(t) + π/8)}` times
the model integral `M(p)` at the fractional part `p = √T - ν`. The inner and outer estimates it
combines are in `Zeta/RiemannSiegel/Inner.lean` and `Zeta/RiemannSiegel/Outer.lean`; the
arbitrary-order chapter `cha:rs_general` rests on that crude estimate and on both of them.

`sec:rsf_sharp` sharpens the saddle estimate to `(61/20) T^{-5/4}` — a gain of `≍ 7 T^{1/2}` —
and lowers its threshold from `T ≥ 10⁶` to `T ≥ 16`, at the cost of retaining the first-order
coefficient `-M'''(p)T^{-1/2}/(96π²)` instead of bounding it away. Feeding it into the order-zero
formula of `Zeta/RiemannSiegel/ZeroOrder.lean` adds the explicit closed-form terms
`(-1)^{ν-1} T^{-1/4} (Ψ(p) + C₁(p)/√T)` to the main sum and improves the error from
`190 T^{-1/4}` to `(25/4) T^{-5/4}`, which at `T = 10⁶` takes the error from `6.0` to
`2.0·10^{-7}` and is what makes certification of individual zeros feasible. Two errors are
incurred: the saddle-point error itself, and the swap of the true phase `θ` for the Stirling
phase `ϑ` carried by the saddle factor, bounded in `Zeta/RiemannSiegel/Theta.lean`.

Siegel's identity (`thm:rsz_siegel`), which the order-zero formula rests on, is proved in
`Zeta/RiemannSiegel/Siegel.lean`, so the whole tower is unconditional.

## Main results

* `Zeta.RiemannSiegel.norm_contourIntegral_sub_modelIntegral_le`
  (`riemann_siegel_first.tex`, `thm:rsf_saddle`);
* `Zeta.RiemannSiegel.norm_contourIntegral_sub_modelIntegral_sub_moment_le`
  (`riemann_siegel_first.tex`, `thm:rsf_saddle_sharp`);
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le`
  (`riemann_siegel_first.tex`, `cor:rsf_formula_sharp`): the first-order formula retaining
  `C₁(p)`, with error `(25/4) T^{-5/4}` for every `t ≥ 32π`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_sub_correction_le`
  (`riemann_siegel_first.tex`, `cor:rsf_formula_drop`): the same with `C₁(p)` dropped;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le`: the
  sharp formula in the form an implementation uses it — main sum at an approximate phase, cutoff
  `ν = ⌊√T⌋`, and the phase error `ε` carried explicitly as a further `4√ν ε`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le'`: the
  same at the order-`2` Stirling phase, where `ε` is discharged and the whole error is the closed
  form `25/4 T^{-5/4} + T^{-15/4}/32`.

Retaining `C₁` is what makes the phase swap affordable at `t ≥ 32π`: the swap multiplies a
*complex* modulus `‖M - M'''ζ/(96π²)‖`, not `|Ψ + C₁ζ|`, which is why
`Zeta/RiemannSiegel/Linear.lean` bounds `M` and `M'''` and not only `Ψ` and `C₁`. The `+` sign on
`C₁` is that of `C₁ = -Ψ'''/(96π²)`, not of the subtraction inside the model term.
-/
@[expose] public section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/-- The `T`-exponent arithmetic behind the `T^{-3/4}` normalisation. -/
private theorem rpow_neg_quarter_div_sqrt {T : ℝ} (hT : 0 < T) :
    T ^ (-(1 / 4) : ℝ) / Real.sqrt T = T ^ (-(3 / 4) : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hT]
  norm_num

/-- The `T`-exponent arithmetic behind the `T^{-5/4}` normalisation. -/
private theorem rpow_neg_quarter_div_self {T : ℝ} (hT : 0 < T) :
    T ^ (-(1 / 4) : ℝ) / T = T ^ (-(5 / 4) : ℝ) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one T, ← Real.rpow_add hT]
  norm_num

/-- **First-order evaluation of the shifted Riemann–Siegel integral**
(`riemann_siegel_first.tex`, `thm:rsf_saddle`). -/
theorem norm_contourIntegral_sub_modelIntegral_le {t : ℝ} (ht : 10 ^ 6 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * modelIntegral ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2)‖
      ≤ 22 * (t / (2 * π)) ^ (-(3 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  -- split at the splitting radius `W = T^{1/12}`; the constants `21` and `1` of the inner and
  -- outer estimates make up the `22`
  have hbound : ‖(1 + I) * ∫ w : ℝ, modelIntegrand ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)‖
      ≤ 22 / Real.sqrt (t / (2 * π)) := by
    rw [← integral_add_compl (s := Set.Icc (-splitRadius t) (splitRadius t)) measurableSet_Icc
      (integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν), mul_add]
    exact (norm_add_le _ _).trans ((add_le_add (norm_integral_inner_le ht hν hν')
      (norm_integral_outer_le ht hν hν')).trans_eq (by ring))
  rw [contourIntegral_sub_mul_modelIntegral ht0 ν, norm_mul, norm_saddleFactor ht0 ν]
  refine (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le _)).trans_eq ?_
  rw [← rpow_neg_quarter_div_sqrt hT0]
  ring

/-! ### The error splitting -/

/-- **The exact splitting of the first-order error** into the phase-swap term and the saddle-point
term, for an arbitrary model term `Y`. It is instantiated at
`Y = M(p) - M'''(p)T^{-1/2}/(96π²)` for `cor:rsf_formula_sharp`: nothing in the splitting
depends on which model term is being approximated, only the two estimates fed into it do. -/
private theorem hardyZ_sub_mainSum_add_two_mul_re_eq {t : ℝ} (ht : 0 < t) (ν : ℕ) (Y : ℂ) :
    hardyZ t - mainSum t ν
        + 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)).re
      = -2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
              * (exp (-((π / 8 : ℝ) * I)) * Y))).re
        - 2 * (exp (I * (riemannSiegelTheta t : ℂ))
            * (contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y)).re := by
  -- the phase `e^{iθ}` meets `e^{-i(ϑ+π/8)}` in the saddle factor and leaves `e^{i(θ-ϑ)}e^{-iπ/8}`
  have hexp : exp (I * (riemannSiegelTheta t : ℂ)) * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))
      = exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) * exp (-((π / 8 : ℝ) * I)) := by
    rw [← exp_add, ← exp_add]
    exact congrArg _ (by push_cast; ring)
  have hkey : exp (I * (riemannSiegelTheta t : ℂ)) * (saddleFactor t ν * Y)
      = ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)
        + ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
              * (exp (-((π / 8 : ℝ) * I)) * Y)) := by
    rw [saddleFactor, show ((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
      = (-1 : ℂ) ^ ν * (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) from by push_cast; ring]
    linear_combination ((-1 : ℂ) ^ ν * (((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) * Y) * hexp
  rw [hardyZ_eq_mainSum_sub ht ν,
    show exp (I * (riemannSiegelTheta t : ℂ))
        * contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
      = exp (I * (riemannSiegelTheta t : ℂ)) * (saddleFactor t ν * Y)
        + exp (I * (riemannSiegelTheta t : ℂ))
            * (contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y) by ring,
    hkey]
  simp only [Complex.add_re]
  ring

/-- The modulus of the saddle factor's scalar, `‖(-1)^ν T^{-1/4}‖ = T^{-1/4}`. -/
private theorem norm_ofReal_neg_one_pow_mul_rpow {t : ℝ} (ht : 0 < t / (2 * π)) (ν : ℕ) :
    ‖((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)‖
      = (t / (2 * π)) ^ (-(1 / 4) : ℝ) := by
  simp [abs_of_pos (Real.rpow_pos_of_pos ht _)]

/-- **The phase-swap error**: replacing `e^{iϑ}` by the true `e^{iθ}` in the saddle factor costs
at most `2T^{-1/4}φB`, where `φ` bounds the phase drift and `B` the model term `Y`. -/
private theorem abs_two_mul_re_phase_swap_le {t : ℝ} (hT0 : 0 < t / (2 * π)) (ν : ℕ) {Y : ℂ}
    {φ B : ℝ} (hY : ‖Y‖ ≤ B)
    (hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖ ≤ φ) :
    |2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
        * ((exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1)
          * (exp (-((π / 8 : ℝ) * I)) * Y))).re|
      ≤ 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (φ * B)) := by
  have hEY : ‖exp (-((π / 8 : ℝ) * I)) * Y‖ ≤ B := by simpa [Complex.norm_exp] using hY
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  rw [norm_mul, norm_mul, norm_ofReal_neg_one_pow_mul_rpow hT0 ν]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hphase hEY (norm_nonneg _)
    ((norm_nonneg _).trans hphase)) (Real.rpow_nonneg hT0.le _)

/-- Multiplying by the unimodular `e^{iθ}` and taking twice a real part cannot exceed `2R`. -/
private theorem abs_two_mul_re_exp_I_mul_le {t R : ℝ} {Z : ℂ} (h : ‖Z‖ ≤ R) :
    |2 * (exp (I * (riemannSiegelTheta t : ℂ)) * Z).re| ≤ 2 * R := by
  rw [abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
  simpa [Complex.norm_exp] using h

/-- **The first-order error assembly**: the phase swap and the saddle-point estimate are the only
two contributions to the distance from `Z(t)` to the main sum corrected by the model term `Y`. -/
private theorem abs_hardyZ_sub_mainSum_add_two_mul_re_le {t : ℝ} (hT0 : 0 < t / (2 * π)) (ν : ℕ)
    {Y : ℂ} {φ B R : ℝ} (hY : ‖Y‖ ≤ B)
    (hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖ ≤ φ)
    (hsaddle : ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2) - saddleFactor t ν * Y‖ ≤ R) :
    |hardyZ t - mainSum t ν
        + 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I)) * Y)).re|
      ≤ 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (φ * B)) + 2 * R := by
  have hb1 := abs_two_mul_re_phase_swap_le hT0 ν hY hphase
  have hb2 := abs_two_mul_re_exp_I_mul_le (t := t) hsaddle
  rw [hardyZ_sub_mainSum_add_two_mul_re_eq
    ((div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0) ν, abs_le]
  rw [abs_le] at hb1 hb2
  constructor <;> linarith

/-! ### The sharp saddle estimate -/

/-- **Sharp first-order evaluation of the shifted Riemann–Siegel integral**
(`riemann_siegel_first.tex`, `thm:rsf_saddle_sharp`). The retained term
`-M'''(p)T^{-1/2}/(96π²)` is the classical `C₁(p)` of the Riemann–Siegel expansion. -/
theorem norm_contourIntegral_sub_modelIntegral_sub_moment_le {t : ℝ} (ht : 16 ≤ t / (2 * π))
    {ν : ℕ} (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    ‖contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * (modelIntegral ((Real.sqrt (t / (2 * π)) - ν : ℝ)) (1 / 2)
            - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2))
                  ((Real.sqrt (t / (2 * π)) - ν : ℝ)) / (96 * (π : ℂ) ^ 2)
                / ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ))‖
      ≤ 61 / 20 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  -- the three regional estimates, the exact factorisation and the two integrands
  have hinner := norm_integral_inner_sub_linear_le ht hν hν'
  have hlin := norm_integral_linear_add_iteratedDeriv_three_modelIntegral_le ht hν hν'
  have houter := norm_integral_outer_le' ht hν hν'
  have hfac := contourIntegral_sub_mul_modelIntegral ht0 ν
  have hFint := integrable_modelIntegrand_mul_exp_saddleDiscrepancy_sub_one ht0 ν
  have hLint := integrable_modelIntegrand_mul_saddleLinear_div
    ((Real.sqrt (t / (2 * π)) - ν : ℝ) : ℂ) ((Real.sqrt (t / (2 * π)) : ℝ) : ℂ)
  -- abbreviations for the saddle `√T`, the fractional part `p` and the splitting radius
  set S : ℝ := Real.sqrt (t / (2 * π))
  set p : ℝ := S - (ν : ℝ)
  set W : ℝ := sharpSplitRadius t
  set D : ℂ := iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
    / (S : ℂ)
  -- the inner estimate is stated for the difference of the two integrands; split it
  rw [funext fun w : ℝ ↦ mul_sub (modelIntegrand (p : ℂ) (1 / 2) w)
      (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)
      (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)),
    integral_sub hFint.integrableOn hLint.integrableOn] at hinner
  -- the whole line is the inner region, the linear term and the outer region
  have hkey : (1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D
      = (1 + I) * ((∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
              * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1))
            - ∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
                * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ)))
        + ((1 + I) * (∫ w in Set.Icc (-W) W, modelIntegrand (p : ℂ) (1 / 2) w
              * (saddleLinear (line (1 / 2) w - (p : ℂ)) / (S : ℂ))) + D)
        + (1 + I) * ∫ w in (Set.Icc (-W) W)ᶜ, modelIntegrand (p : ℂ) (1 / 2) w
              * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1) := by
    rw [← integral_add_compl measurableSet_Icc hFint]
    ring
  have hbound : ‖(1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
        * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D‖
      ≤ 61 / 20 / (t / (2 * π)) := by
    rw [hkey]
    refine norm_add₃_le.trans ((add_le_add (add_le_add hinner hlin) houter).trans ?_)
    -- `299/100 + 1/200 + 1/20 = 3045/1000 ≤ 61/20`
    rw [← add_div, ← add_div, div_le_div_iff_of_pos_right hT0]
    norm_num
  rw [show contourIntegral (1 / 2 + t * I) ((ν : ℝ) + 1 / 2)
        - saddleFactor t ν * (modelIntegral (p : ℂ) (1 / 2) - D)
      = saddleFactor t ν * ((1 + I) * (∫ w : ℝ, modelIntegrand (p : ℂ) (1 / 2) w
          * (exp (saddleDiscrepancy t (line ((ν : ℝ) + 1 / 2) w)) - 1)) + D) by
      linear_combination hfac,
    norm_mul, norm_saddleFactor ht0 ν]
  refine (mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le _)).trans_eq ?_
  rw [← rpow_neg_quarter_div_self hT0]
  ring

/-! ### The sharp first-order formula -/

/-- The real part the sharp model term `M(p) - M'''(p)/(96π²)/S` contributes: `Ψ(p) + C₁(p)/S`. -/
private theorem two_mul_re_exp_mul_modelIntegral_sub_moment_eq (p : ℝ) {S : ℝ} (hS : 0 < S) :
    2 * (exp (-((π / 8 : ℝ) * I))
        * (modelIntegral (p : ℂ) (1 / 2)
            - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
              / (S : ℂ))).re
      = correction p + correctionLinear p / S := by
  have hSC : ((S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hS.ne'
  have hsplit : exp (-((π / 8 : ℝ) * I))
      * (modelIntegral (p : ℂ) (1 / 2)
          - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
            / (S : ℂ))
      = exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)
        + ((-(1 / (96 * π ^ 2 * S)) : ℝ) : ℂ)
            * (exp (-((π / 8 : ℝ) * I))
                * iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [correctionLinear_eq, iteratedDeriv_three_correction p, hsplit, Complex.add_re,
    Complex.re_ofReal_mul, correction]
  field_simp

/-- **The sharp first-order Riemann–Siegel formula** (`riemann_siegel_first.tex`,
`cor:rsf_formula_sharp`), retaining the classical coefficient `C₁(p)T^{-1/2}` alongside `Ψ(p)`. -/
theorem abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    |hardyZ t - mainSum t ν
        + (-1) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ν)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ν) / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) := by
  have hpi := Real.pi_gt_three
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  have ht32 : 32 * π ≤ t := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)] at ht
    linarith
  have hS0 : (0 : ℝ) < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  have hS4 : (4 : ℝ) ≤ Real.sqrt (t / (2 * π)) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hp0 : 0 ≤ Real.sqrt (t / (2 * π)) - (ν : ℝ) := by linarith
  have hp1 : Real.sqrt (t / (2 * π)) - (ν : ℝ) ≤ 1 := by linarith
  have hR0 : (0 : ℝ) ≤ (t / (2 * π)) ^ (-(5 / 4) : ℝ) := Real.rpow_nonneg hT0.le _
  have hphase : ‖exp (I * ((riemannSiegelTheta t - leadingTheta t : ℝ) : ℂ)) - 1‖
      ≤ 101 / (4800 * t) :=
    (Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq (Real.norm_eq_abs _)).trans
      (abs_riemannSiegelTheta_sub_leading_le' ht32)
  have hsaddle := norm_contourIntegral_sub_modelIntegral_sub_moment_le ht hν hν'
  set S : ℝ := Real.sqrt (t / (2 * π))
  set p : ℝ := S - (ν : ℝ)
  set Y : ℂ := modelIntegral (p : ℂ) (1 / 2)
    - iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ) / (96 * (π : ℂ) ^ 2)
      / (S : ℂ)
  -- `‖M(p) - M'''(p)ζ/(96π²)‖ ≤ 11/10 + 610/(96π²·4) ≤ 13/10`
  have hY : ‖Y‖ ≤ 13 / 10 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS0, norm_mul,
      norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_div]
    -- `5 · 610 = 3050 ≤ 96π²·4 ≤ 96π²S`
    have hstep : ‖iteratedDeriv 3 (fun q : ℂ ↦ modelIntegral q (1 / 2)) (p : ℂ)‖
        / (96 * π ^ 2 * S) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)]
      nlinarith [norm_iteratedDeriv_three_modelIntegral_le' hp0 hp1,
        mul_le_mul_of_nonneg_right (by nlinarith : (9 : ℝ) ≤ π ^ 2) hS0.le, hS4]
    linarith [norm_modelIntegral_le' hp0 hp1]
  -- the model term the splitting produces is `Ψ(p) + C₁(p)/√T`
  have hre : 2 * (((((-1 : ℝ)) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ) : ℂ)
        * (exp (-((π / 8 : ℝ) * I)) * Y)).re
      = (-1) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ) * (correction p + correctionLinear p / S) := by
    rw [Complex.re_ofReal_mul]
    linear_combination ((-1 : ℝ) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ))
      * two_mul_re_exp_mul_modelIntegral_sub_moment_eq p hS0
  rw [← hre]
  refine (abs_hardyZ_sub_mainSum_add_two_mul_re_le hT0 ν hY hphase hsaddle).trans ?_
  -- `2 · (13/10) · (101/4800) / (2π) = 1313/(48000π) ≤ 1/50`, and `61/10 + 1/50 = 153/25 ≤ 25/4`
  rw [show 2 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) * (101 / (4800 * t) * (13 / 10)))
      = 1313 / (24000 * (2 * π)) * (t / (2 * π)) ^ (-(5 / 4) : ℝ) from by
    rw [← rpow_neg_quarter_div_self hT0]
    field_simp
    ring]
  have hcoef : (1313 : ℝ) / (24000 * (2 * π)) ≤ 1 / 50 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hR0]

/-- **The sharp first-order formula with `C₁` dropped** (`riemann_siegel_first.tex`,
`cor:rsf_formula_drop`), the discarded `C₁(p)` reappearing as the leading `T^{-3/4}` error. -/
theorem abs_hardyZ_sub_mainSum_sub_correction_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) {ν : ℕ}
    (hν : (ν : ℝ) ≤ Real.sqrt (t / (2 * π)))
    (hν' : Real.sqrt (t / (2 * π)) ≤ ν + 1) :
    |hardyZ t - mainSum t ν
        + (-1) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * correction (Real.sqrt (t / (2 * π)) - ν)|
      ≤ 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ) + 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have hS0 : (0 : ℝ) < Real.sqrt (t / (2 * π)) := Real.sqrt_pos.2 hT0
  have hp0 : 0 ≤ Real.sqrt (t / (2 * π)) - (ν : ℝ) := by linarith
  have hp1 : Real.sqrt (t / (2 * π)) - (ν : ℝ) ≤ 1 := by linarith
  -- the discarded term is `(-1)^ν T^{-1/4} C₁(p)/√T`, of modulus `≤ (13/10) T^{-3/4}`
  have hdrop : |(-1 : ℝ) ^ ν * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * (correctionLinear (Real.sqrt (t / (2 * π)) - ν) / Real.sqrt (t / (2 * π)))|
      ≤ 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hT0 _), abs_div, abs_of_pos hS0,
      ← rpow_neg_quarter_div_sqrt hT0,
      show (13 : ℝ) / 10 * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) / Real.sqrt (t / (2 * π)))
        = (t / (2 * π)) ^ (-(1 / 4) : ℝ) * (13 / 10 / Real.sqrt (t / (2 * π))) by ring]
    gcongr
    exact abs_correctionLinear_le hp0 hp1
  have hsharp := abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le ht hν hν'
  rw [abs_le] at hsharp hdrop ⊢
  constructor <;> linarith

/-- **The sharp first-order formula at an approximate phase**, with the cutoff `ν = ⌊√T⌋`
and the phase error `ε` carried explicitly. -/
theorem abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) {θ' ε : ℝ} (hθ : |riemannSiegelTheta t - θ'| ≤ ε) :
    |hardyZ t - mainSumOfPhase θ' t ⌊Real.sqrt (t / (2 * π))⌋₊
        + (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
                  / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ)
        + 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * ε := by
  have hsharp := abs_hardyZ_sub_mainSum_sub_correction_sub_correctionLinear_le ht
    (Nat.floor_le (Real.sqrt_nonneg (t / (2 * π)))) (Nat.lt_floor_add_one _).le
  have hlip : |mainSum t ⌊Real.sqrt (t / (2 * π))⌋₊
      - mainSumOfPhase θ' t ⌊Real.sqrt (t / (2 * π))⌋₊|
      ≤ 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * ε := by
    rw [mainSum_eq_mainSumOfPhase]
    exact (abs_mainSumOfPhase_sub_mainSumOfPhase_le _ _ t _).trans
      (mul_le_mul_of_nonneg_left hθ (by positivity))
  rw [abs_le] at hsharp hlip ⊢
  constructor <;> linarith

/-- **The sharp first-order formula with the phase error discharged**: the main sum evaluated at
the order-`2` Stirling approximant of `θ`, with no free parameter and no side condition beyond
`t ≥ 32π`. -/
theorem abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le' {t : ℝ}
    (ht : 16 ≤ t / (2 * π)) :
    |hardyZ t
        - mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
        + (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
            * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
                  / Real.sqrt (t / (2 * π)))|
      ≤ 25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ)
        + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by
  have hT0 : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * π)).mp hT0
  refine (abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le ht
    (abs_riemannSiegelTheta_sub_approximant_two_le ht0)).trans ?_
  -- `4√ν · 12t^{-4} ≤ 48 T^{1/4}/((2π)^4 T^4) = 48/(2π)^4 · T^{-15/4} ≤ T^{-15/4}/32`
  have hq : Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ ≤ (t / (2 * π)) ^ (1 / 4 : ℝ) := by
    refine (Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg _))).trans ?_
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    norm_num
  have hpow : (t / (2 * π)) ^ (1 / 4 : ℝ) / (t / (2 * π)) ^ (4 : ℕ)
      = (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by
    rw [← Real.rpow_natCast (t / (2 * π)) 4, ← Real.rpow_sub hT0]
    norm_num
  have ht4 : t ^ 4 = (2 * π) ^ 4 * (t / (2 * π)) ^ 4 := by
    rw [div_pow, mul_div_cancel₀ _ (by positivity : ((2 : ℝ) * π) ^ 4 ≠ 0)]
  have hcoef : (48 : ℝ) / (2 * π) ^ 4 ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6.28)
      (by linarith [Real.pi_gt_d2] : (6.28 : ℝ) ≤ 2 * π) 4]
  refine add_le_add le_rfl ?_
  calc 4 * Real.sqrt ⌊Real.sqrt (t / (2 * π))⌋₊ * (12 / t ^ 4)
      ≤ 4 * (t / (2 * π)) ^ (1 / 4 : ℝ) * (12 / t ^ 4) := by gcongr
    _ = 48 / (2 * π) ^ 4 * ((t / (2 * π)) ^ (1 / 4 : ℝ) / (t / (2 * π)) ^ (4 : ℕ)) := by
        rw [ht4]
        field_simp
        ring
    _ = 48 / (2 * π) ^ 4 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) := by rw [hpow]
    _ ≤ 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hT0.le _)

end Zeta.RiemannSiegel

open Zeta.RiemannSiegel

/-! ### The packaged approximant

`abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le'` in the form a certificate
consumes it: one approximant, one error bound, and the theorem that the second bounds the first's
distance from `Z`. This mirrors `hardyZApproximantEM` / `hardyZErrorBoundEM` /
`abs_hardyZRemainderEM_le` on the Euler–Maclaurin side, so both methods present the same interface
to `Zeta.Certificates`. The `EM`/`RS` suffixes, rather than the namespace, carry the
disambiguation: the two families are siblings and a certificate file uses both. -/

/-- **The rigorous first-order Riemann–Siegel error bound.** For every `t ≥ 32π`,
`|Z(t) − Z̃^{RS}(t)| ≤ hardyZErrorBoundRS t`. This is the Riemann–Siegel analogue of
`abs_hardyZRemainderEM_le`, and the only fact about the approximant that certifying a sign change
requires. -/
theorem abs_hardyZRemainderRS_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    |hardyZRemainderRS t| ≤ hardyZErrorBoundRS t := by
  refine (le_of_eq (congrArg abs ?_)).trans
    (abs_hardyZ_sub_mainSumOfPhase_sub_correction_sub_correctionLinear_le' ht)
  ring


/-! ### The zeroth-order (linear-free) approximant

`correctionLinear` is defined through `modelMoment`, and its closed form — obtained by
differentiating `cos_mul_correction` three times — divides by `cos(2πp)` four times over, so an
interval evaluation of it loses ~4 orders of cancellation wherever `p` approaches `1/4` or `3/4`.
Since `|C₁| ≤ 13/10` uniformly, dropping the term and charging its size
`T^{-1/4}·(13/10)/√T = (13/10)T^{-3/4}` to the error bound is far cheaper.

This drops a rung on the Riemann–Siegel ladder: truncating after `C_k` gives error
`O(T^{-(2k+3)/4})`, so the bound degrades from the first-order `O(T^{-5/4})` to the zeroth-order
`O(T^{-3/4})` (the main sum alone is `O(T^{-1/4})`, `abs_hardyZ_sub_mainSum_le_threeHundredTwo`).
At the heights in use that costs a factor ~2 at the bottom of the Riemann–Siegel range
(`t ≈ 150`: `0.119 → 0.239`) and ~4 at the top (`t ≈ 1420`: `0.0071 → 0.029`), where the bound is
tiny anyway; the gap grows like `√T`, so `correctionLinear` would have to return well above 1420.
The constant is also not the sharp zeroth-order one — this is the first-order remainder plus the
discarded term's maximum, not a direct `k = 0` analysis. -/

/-- **The rigorous error bound for the linear-free approximant.** For every `t ≥ 32π`,
`|Z(t) − Z̃₀^{RS}(t)| ≤ hardyZErrorBoundRS₀ t`: the first-order bound plus `abs_correctionLinear_le`
on the discarded term. -/
theorem abs_hardyZRemainderRS₀_le {t : ℝ} (ht : 16 ≤ t / (2 * π)) :
    |hardyZRemainderRS₀ t| ≤ hardyZErrorBoundRS₀ t := by
  have hT : (0 : ℝ) < t / (2 * π) := lt_of_lt_of_le (by norm_num) ht
  set T := t / (2 * π) with hTdef
  set ν := ⌊Real.sqrt T⌋₊ with hνdef
  set p := Real.sqrt T - (ν : ℝ) with hpdef
  have hp0 : 0 ≤ p := sub_nonneg.2 (Nat.floor_le (Real.sqrt_nonneg T))
  have hp1 : p ≤ 1 := by
    have := Nat.lt_floor_add_one (Real.sqrt T)
    rw [hpdef]; linarith
  -- `R₀ = R − Y`: the linear-free remainder differs from the full one by the discarded term.
  have hsplit : hardyZRemainderRS₀ t
      = hardyZRemainderRS t
        - (-1) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T) := by
    simp only [hardyZRemainderRS₀, hardyZRemainderRS, hardyZApproximantRS₀, hardyZApproximantRS,
      ← hTdef, ← hνdef, ← hpdef]
    ring
  have hsqrtT : Real.sqrt T = T ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow T
  have hdrop : |(-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T)|
      ≤ 13 / 10 * T ^ (-(3 / 4) : ℝ) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div,
      abs_of_pos (Real.rpow_pos_of_pos hT _), abs_of_pos (Real.sqrt_pos.2 hT), hsqrtT]
    have hpos : (0 : ℝ) < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT _
    calc T ^ (-(1 / 4) : ℝ) * (|correctionLinear p| / T ^ (1 / 2 : ℝ))
        ≤ T ^ (-(1 / 4) : ℝ) * (13 / 10 / T ^ (1 / 2 : ℝ)) := by
          gcongr
          exact abs_correctionLinear_le hp0 hp1
      _ = 13 / 10 * (T ^ (-(1 / 4) : ℝ) / T ^ (1 / 2 : ℝ)) := by ring
      _ = 13 / 10 * T ^ (-(3 / 4) : ℝ) := by rw [← Real.rpow_sub hT]; norm_num
  calc |hardyZRemainderRS₀ t|
      = |hardyZRemainderRS t
          + -((-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T))| := by
        rw [hsplit, sub_eq_add_neg]
    _ ≤ |hardyZRemainderRS t|
          + |(-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T)| := by
        rw [← abs_neg ((-1 : ℝ) ^ ν * T ^ (-(1 / 4) : ℝ) * (correctionLinear p / Real.sqrt T))]
        exact abs_add_le _ _
    _ ≤ hardyZErrorBoundRS t + 13 / 10 * T ^ (-(3 / 4) : ℝ) :=
        add_le_add (abs_hardyZRemainderRS_le ht) hdrop
