/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Hadamard.HadamardConcrete
public import Zeta.Hadamard.CartanMinModulus
public import Zeta.Hadamard.XiOrder
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PrimeNumberTheoremAnd.BorelCaratheodory

/-!
# Growth of the exponent of the Hadamard factorisation of `ξ`

Writing `ξ = exp(h) · P` with `h` entire and `P` the canonical product, this file bounds the real
part of `h` on a suitable circle (`hadamard_factorization.tex`).

## Main result

* `re_log_riemannXi_div_canonicalProduct_le` (`lem:hf_reH_growth`): on a suitable circle
  `|s| = R' ∈ [R, 2R]`, `Re h(s) ≤ C·R^{3/2}`.
-/
@[expose] public section


open Complex Filter Topology Set Metric


/-- **Real-part growth of the exponent (`lem:hf_reH_growth`).** If `ξ = exp(h) · P` with `h` entire
and `P` the canonical product of the zeros of `ξ`, then there is `C > 0` such that for every `R ≥ 2`
there is a radius `R' ∈ [R, 2R]` on whose circle `Re h(s) ≤ C · R^{3/2}`. -/
theorem re_log_riemannXi_div_canonicalProduct_le {h : ℂ → ℂ}
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (h s).re ≤ C * R ^ (3 / 2 : ℝ) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  obtain ⟨CP, hCP, hP⟩ := exists_circle_log_norm_riemannXiCanonicalProduct_ge
  refine ⟨Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP, by positivity, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hP R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hPne, hlogP⟩ := hR' s hs
  set P := riemannXiCanonicalProduct riemannXiZeros
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hs ▸ hR.trans hR'mem.1
  have hPpos : 0 < ‖P s‖ := norm_pos_iff.mpr hPne
  -- `‖ξ(s)‖ = exp(Re h(s)) · ‖P(s)‖ > 0`, so `Re h(s) = log‖ξ(s)‖ - log‖P(s)‖`.
  have hnormξ : ‖riemannXi s‖ = Real.exp ((h s).re) * ‖P s‖ := by
    rw [hrep s, norm_mul, Complex.norm_exp]
  have hξpos : 0 < ‖riemannXi s‖ := by rw [hnormξ]; positivity
  have hre_eq : (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := by
    rw [hnormξ, Real.log_mul (Real.exp_pos _).ne' hPpos.ne', Real.log_exp, add_sub_cancel_right]
  -- Upper bound on `log‖ξ(s)‖`, via `‖s‖ · log‖s‖ ≤ 2‖s‖^{3/2} ≤ 2·(2R)^{3/2}`.
  have hlogξ : Real.log ‖riemannXi s‖ ≤ Cξ * (‖s‖ * Real.log ‖s‖) :=
    (Real.log_le_iff_le_exp hξpos).2 (hξ s hs2)
  have hsl : ‖s‖ * Real.log ‖s‖ ≤ 2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hR0]
    have hlog : Real.log ‖s‖ ≤ 2 * ‖s‖ ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (norm_nonneg s) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hmul : ‖s‖ * ‖s‖ ^ (1 / 2 : ℝ) = ‖s‖ ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have hpow : ‖s‖ ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg s) (hs ▸ hR'mem.2) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hlog (norm_nonneg s)]
  calc (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := hre_eq
    _ ≤ Cξ * (‖s‖ * Real.log ‖s‖) + CP * R ^ (3 / 2 : ℝ) := by linarith
    _ ≤ Cξ * (2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ))) + CP * R ^ (3 / 2 : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hsl hCξ.le]
    _ = (Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP) * R ^ (3 / 2 : ℝ) := by ring

