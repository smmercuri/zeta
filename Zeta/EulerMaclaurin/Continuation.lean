/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.EulerMaclaurin.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Convex

/-!
# Analytic continuation of the Euler–Maclaurin expansion of `ζ`

The Euler–Maclaurin expansion of `ζ` on the punctured strip `Re s > -(2M+1)`, `s ≠ 1`, carrying
the analytically continued remainder (one order-raising integration by parts past the region
`Re s > 1` of `riemannZeta_eq_of_one_lt_re`).

## Main definitions

- `zetaEMExpansion`: the analytic Euler–Maclaurin right-hand side `E_M(s,N)`, split by
  `zetaEMExpansion_eq_approximant_add_remainder` into the computed `zetaApproximant` and the
  error term `zetaRemainder`.

## Main results

- `Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow`: the order-`p` improper remainder
  `s ↦ Complex.eulerMaclaurinRemainderIoi p f_s N` is holomorphic on `{Re s > 1 - p}`.
- `analyticOnNhd_zetaEMExpansion`: `E_M(·,N)` is analytic on `{Re s > -(2M+1)} \ {1}`.
- `riemannZeta_eq`, `riemannZeta_eq_approximant_add_remainder`: the continued expansion.
- `riemannZeta_eq_order_one`: the first-order case
  `ζ(s) = 1/(s-1) + 1/2 + Complex.eulerMaclaurinRemainderIoi 1 f_s 1` on `Re s > 0`, `s ≠ 1`.
- `riemannZeta_ofReal_re_neg_of_mem_Ioo`: `Re ζ(x) < 0` for real `x ∈ (0, 1)`.
-/
@[expose] public section


open MeasureTheory Filter Topology
open scoped Nat

namespace Complex

/-- Closed form of the improper `ζ`-summand remainder. With `f_s y = (y : ℂ)^(-s)`,
`Complex.eulerMaclaurinRemainderIoi p f_s N = -(s)_p/p! · ∫_N^∞ B̃_p(x) · x^{-s-p} dx`. -/
theorem eulerMaclaurinRemainderIoi_cpow_eq (s : ℂ) (p N : ℕ) :
    Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = -(ascPochhammer ℂ p).eval s / (p ! : ℂ)
          * ∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)) := by
  rw [Complex.eulerMaclaurinRemainderIoi]
  have step1 : (∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x)
      = ∫ x in Set.Ioi (N : ℝ), ((-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s)
          * ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg N) (Set.mem_Ioi.mp hx)
    dsimp only
    rw [Complex.iteratedDeriv_cpow_ofReal_neg s p hx0]
    ring
  rw [step1, integral_const_mul]
  have h2 : (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ p = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨p, by ring⟩
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  field_simp
  linear_combination ((ascPochhammer ℂ p).eval s *
    ∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) * h2

/-- Holomorphy of the order-`p` improper remainder integral. For `1 ≤ N`, the map
`s ↦ Complex.eulerMaclaurinRemainderIoi p f_s N` (with `f_s y = (y:ℂ)^(-s)`) is holomorphic on
the open half-plane `{Re s > 1 - p}`. -/
theorem differentiableOn_eulerMaclaurinRemainderIoi_cpow (p N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
      {s : ℂ | (1 : ℝ) - p < s.re} := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- The periodized Bernoulli kernel is measurable, and each complex power `x ↦ (x:ℂ)^w` is
  -- a.e.-strongly-measurable on `(N, ∞)`; both facts are reused several times below.
  have hker := Complex.measurable_bernoulliFun_fract p
  have hcpowmeas := Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N)
  -- Rewrite `eulerMaclaurinRemainderIoi p f_s N = -(s)_p/p! · G s`: the prefactor is entire, and
  -- `G` is holomorphic on the half-plane by differentiation under the integral sign.
  simp only [eulerMaclaurinRemainderIoi_cpow_eq]
  refine (((ascPochhammer ℂ p).differentiable.neg.div_const (p ! : ℂ)).differentiableOn).mul
    fun s₀ hs₀ ↦ ?_
  rw [Set.mem_ofPred_eq] at hs₀
  -- Choose `σ₁` with `1 - p < σ₁ < Re s₀`, and `ε` so that `σ₁ + p - ε > 1`.
  obtain ⟨σ₁, hσlo, hσhi⟩ : ∃ σ₁ : ℝ, (1 : ℝ) - p < σ₁ ∧ σ₁ < s₀.re :=
    ⟨((1 - p) + s₀.re) / 2, by linarith, by linarith⟩
  set ε : ℝ := (σ₁ + p - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hexp : (1 : ℝ) < σ₁ + p - ε := by rw [hεdef]; linarith
  -- A bound `C ≥ 0` on the periodized Bernoulli kernel.
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_bernoulliFun_fract_le p
  -- Differentiate under the integral sign on the neighbourhood `{Re s > σ₁}` of `s₀`.
  have happ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (F := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))
    (F' := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ)
      * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1)))
    (x₀ := s₀) (bound := fun x ↦ C / ε * x ^ (-(σ₁ + p - ε)))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσhi)
    -- (1) measurability of `F s` near `s₀`
    (Filter.Eventually.of_forall fun s ↦ hker.aestronglyMeasurable.mul (hcpowmeas _))
    -- (2) integrability of `F s₀`
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN
      (by rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith))
    -- (3) measurability of `F' s₀`
    (hker.aestronglyMeasurable.mul
      (((hcpowmeas _).mul
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable).mul
          aestronglyMeasurable_const))
    -- (4) the uniform bound on `F'`
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      have hx1 : (1 : ℝ) ≤ x :=
        le_of_lt (lt_of_le_of_lt (by exact_mod_cast hN) (Set.mem_Ioi.mp hx))
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
      rw [show ‖(bernoulliFun p (Int.fract x) : ℂ)
                * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1))‖
              = ‖(bernoulliFun p (Int.fract x) : ℂ)‖ * x ^ (-s.re - p) * Real.log x from by
            rw [← Complex.ofReal_log hx0.le]
            simp only [norm_mul, norm_neg, norm_one, mul_one,
              Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
              Complex.sub_re, Complex.neg_re, Complex.natCast_re, abs_of_nonneg hlog]
            ring,
        show C / ε * x ^ (-(σ₁ + p - ε)) = C * x ^ (-σ₁ - p) * (x ^ ε / ε) from by
          rw [show -(σ₁ + p - ε) = -σ₁ - p + ε from by ring, Real.rpow_add hx0]; ring]
      exact mul_le_mul (mul_le_mul (hC x) (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
          (Real.rpow_nonneg hx0.le _) hC0) (Real.log_le_rpow_div hx0.le hεpos) hlog
        (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _)))
    -- (5) integrability of the bound
    ((integrableOn_Ioi_rpow_of_lt (a := -(σ₁ + p - ε)) (by linarith) hN0).const_mul (C / ε))
    -- (6) the `s`-derivative
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
      have hbase : (x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le).ne'
      exact HasDerivAt.const_mul _
        ((Complex.hasStrictDerivAt_const_cpow (Or.inl hbase)).hasDerivAt.comp s
          (by simpa using (hasDerivAt_id s).neg.sub_const (p : ℂ))))
  exact happ.2.differentiableAt.differentiableWithinAt

/-- Finite order-raising step for the `ζ`-summand remainder. For `1 ≤ N ≤ R`, the
order-`(2M+1)` remainder over `[N, R]` equals the order-`(2M+2)` one plus the Bernoulli
boundary term of index `2M+2`. -/
private theorem eulerMaclaurinRemainder_cpow_succ (s : ℂ) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (R : ℝ)
              - iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
        + eulerMaclaurinRemainder (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
            (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hderiv : ∀ q, q < 2 * M + 2 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q hx
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 2 →
      IntervalIntegrable (iteratedDeriv q f) volume ((N : ℤ) : ℝ)
        (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) :=
    fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q
        (hpos hx)).continuousAt.continuousWithinAt
  have h1 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by lia)
    (fun q _ x hx ↦ hderiv q (by lia) x (hpos hx)) (fun q hq0 hq ↦ hint q hq0 (by lia))
  have h2 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 2) (by lia)
    (fun q hq x hx ↦ hderiv q hq x (hpos hx)) hint
  rw [hRN, hNa, show (2 * M + 1) / 2 + 1 = M + 1 from by lia] at h1
  rw [hRN, hNa, show (2 * M + 2) / 2 + 1 = M + 1 + 1 from by lia,
    Finset.sum_Ico_succ_top (show (1 : ℕ) ≤ M + 1 by lia)] at h2
  simp only [show 2 * (M + 1) = 2 * M + 2 from by ring,
    show 2 * M + 2 - 1 = 2 * M + 1 from by lia] at h2
  linear_combination h2 - h1

/-- Order-raising on the improper `ζ`-remainder, `2M+1 → 2M+2`. For `1 ≤ N` and `Re s > -2M`
(where the order-`(2M+1)` integral still converges),
`R^∞_{2M+1}(f_s; N) = B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)} + R^∞_{2M+2}(f_s; N)`,
the first summand being the first omitted even Bernoulli term `t_{M+1}(s, N)`. -/
theorem eulerMaclaurinRemainderIoi_succ_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M : ℝ) < s.re) :
    Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * M + 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  set c : ℂ := -s - ((2 * M + 1 : ℕ) : ℂ) with hc
  set B : ℂ := ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
  set P : ℂ := (ascPochhammer ℂ (2 * M + 1)).eval s with hP
  have hcre : c.re < 0 := by
    rw [hc, Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; linarith
  -- Both finite remainders converge to their improper counterparts.
  have hrem : ∀ q : ℕ, 1 < s.re + (q : ℝ) →
      Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder q f (N : ℝ) (R : ℝ)) atTop
        (𝓝 (Complex.eulerMaclaurinRemainderIoi q f (N : ℝ))) := fun q hq ↦ by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s q N hN hq)
      tendsto_natCast_atTop_atTop).const_mul _
  -- The order-`(2M+1)` derivative in closed form; its value at `R` tends to `0`.
  have hcf : ∀ R : ℕ, 1 ≤ R → iteratedDeriv (2 * M + 1) f (R : ℝ) = -P * (R : ℂ) ^ c := by
    intro R hR
    rw [hf, Complex.iteratedDeriv_cpow_ofReal_neg s (2 * M + 1)
        (by exact_mod_cast hR : (0 : ℝ) < R),
      Odd.neg_one_pow ⟨M, by ring⟩, hc, hP]
    push_cast; ring
  have hbdy : Tendsto (fun R : ℕ ↦ B * (iteratedDeriv (2 * M + 1) f (R : ℝ)
        - iteratedDeriv (2 * M + 1) f (N : ℝ))) atTop (𝓝 (B * P * (N : ℂ) ^ c)) := by
    have hbase := (((tendsto_natCast_cpow_nhds_zero hcre).const_mul (-P)).sub_const
      (-P * (N : ℂ) ^ c)).const_mul B
    rw [show B * (-P * 0 - -P * (N : ℂ) ^ c) = B * P * (N : ℂ) ^ c from by ring] at hbase
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [hcf R (le_trans hN hR), hcf N hN]
  refine tendsto_nhds_unique (Tendsto.congr' ?_ (hrem (2 * M + 1) (by push_cast; linarith)))
    (hbdy.add (hrem (2 * M + 2) (by push_cast; linarith)))
  filter_upwards [eventually_ge_atTop N] with R hR
  exact eulerMaclaurinRemainder_cpow_succ s M N R hN hR

/-- The order-`1` Euler–Maclaurin remainder of `ζ` at a positive real point has norm at most
`1/2`. -/
theorem norm_eulerMaclaurinRemainderIoi_one_ofReal_le {x : ℝ} (hx0 : 0 < x) :
    ‖Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-(x : ℂ))) 1‖ ≤ 1 / 2 := by
  have h := eulerMaclaurinRemainderIoi_cpow_eq (x : ℂ) 1 1
  simp only [Nat.cast_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_one, div_one] at h
  have hb := norm_integral_le_of_norm_le
    (f := fun y : ℝ ↦ (bernoulliFun 1 (Int.fract y) : ℂ) * (y : ℂ) ^ (-(x : ℂ) - 1))
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    ((integrableOn_Ioi_rpow_of_lt (show -x - 1 < -1 by linarith) one_pos).const_mul (1 / 2)) ?_
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -x - 1 + 1 = -x from by ring, neg_div_neg_eq] at hb
    rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    refine (mul_le_mul_of_nonneg_left hb hx0.le).trans_eq ?_
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := one_pos.trans hy
    have hre : (-(x : ℂ) - 1).re = -x - 1 := by simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      hre, bernoulliFun_one]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [Int.fract_nonneg y], ?_⟩)
      (Real.rpow_nonneg hy0.le _)
    linarith [Int.fract_lt_one y]

end Complex

/-- The analytic Euler–Maclaurin right-hand side for `ζ`,
`E_M(s,N) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
              + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}
              + B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)}
              + Complex.eulerMaclaurinRemainderIoi (2M+2) f_s N`,
whose last two summands form the analytically continued remainder
`R_M(s,N) = t_{M+1}(s,N) + R^∞_{2M+2}(f_s; N)`. -/
noncomputable def zetaEMExpansion (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
    + ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)

/-- The Euler–Maclaurin approximant for `ζ`, the computed main term of the order-`M`,
cutoff-`N` expansion:
`A_M(s,N) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
              + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}`. -/
noncomputable abbrev zetaApproximant (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))

/-- The Euler–Maclaurin remainder for `ζ`, the error term of the order-`M`, cutoff-`N`
expansion: `R_M(s,N) = t_{M+1}(s,N) + R^∞_{2M+2}(f_s; N)`, with `t_{M+1}` the leading uncomputed
Bernoulli term. It is bounded by `norm_zetaRemainder_le`. -/
noncomputable abbrev zetaRemainder (s : ℂ) (M N : ℕ) : ℂ :=
  ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
      * (ascPochhammer ℂ (2 * M + 1)).eval s
      * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)

/-- The Euler–Maclaurin right-hand side `zetaEMExpansion` splits as its approximant plus its
remainder. -/
theorem zetaEMExpansion_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) :
    zetaEMExpansion s M N = zetaApproximant s M N + zetaRemainder s M N := by
  rw [zetaEMExpansion, zetaApproximant, zetaRemainder]; ring

/-- Analyticity of the continued Euler–Maclaurin right-hand side. For `1 ≤ N`, the map
`s ↦ zetaEMExpansion s M N` is analytic on the punctured strip `{Re s > -(2M+1)} \ {1}`. -/
theorem analyticOnNhd_zetaEMExpansion (M N : ℕ) (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ zetaEMExpansion s M N)
      ({s : ℂ | (-(2 * M + 1 : ℝ)) < s.re} \ {1}) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  refine DifferentiableOn.analyticOnNhd ?_
    ((isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton)
  simp only [zetaEMExpansion]
  refine DifferentiableOn.add (DifferentiableOn.add (DifferentiableOn.add
    (DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_) ?_) ?_) ?_
  · -- `∑_{n=1}^{N-1} n^{-s}`
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun n hn ↦ ?_)
    have : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Ico] at hn; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn.1
    exact differentiable_id.neg.const_cpow (Or.inl this)
  · -- `N^{1-s}/(s-1)`
    apply DifferentiableOn.div
    · exact (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
        (Or.inl hNne)).differentiableOn
    · exact (differentiable_id.sub_const 1).differentiableOn
    · intro s hs; exact sub_ne_zero.mpr hs.2
  · -- `N^{-s}/2`
    exact ((differentiable_id.neg.const_cpow (Or.inl hNne)).div_const 2).differentiableOn
  · -- `∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)}`
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun k _ ↦ ?_)
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * k - 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  · -- `t_{M+1}` term
    refine Differentiable.differentiableOn ?_
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * M + 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  · -- the order-`(2M+2)` remainder
    refine (Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow (2 * M + 2) N hN).mono
      fun s hs ↦ ?_
    have hs1 : (-(2 * M + 1 : ℝ)) < s.re := hs.1
    rw [Set.mem_ofPred_eq]
    push_cast
    linarith

/-- Euler–Maclaurin expansion of `ζ` on the punctured strip `Re s > -(2M+1)`. For `1 ≤ N`,
`Re s > -(2M+1)` and `s ≠ 1`, `ζ(s) = zetaEMExpansion s M N`, i.e.
`ζ(s) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
          + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)} + R_M(s, N)`. -/
theorem riemannZeta_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = zetaEMExpansion s M N := by
  set H : Set ℂ := {z : ℂ | (-(2 * M + 1 : ℝ)) < z.re} with hHdef
  set U : Set ℂ := H \ {1} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hUopen
  have hE : AnalyticOnNhd ℂ (fun z ↦ zetaEMExpansion z M N) U :=
    analyticOnNhd_zetaEMExpansion M N hN
  -- Preconnectedness of the punctured half-plane, via four convex half-space pieces glued at
  -- `I`, `-I` and `2 + I`.
  have hP : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  have hcH : Convex ℝ H := convex_halfSpace_re_gt _
  have hmH : ∀ z : ℂ, 0 ≤ z.re → z ∈ H := fun z hz ↦ by
    simp only [hHdef, Set.mem_ofPred_eq]; linarith [hP]
  have hA : IsPreconnected ({z : ℂ | 0 < z.im} ∩ H) :=
    ((convex_halfSpace_im_gt 0).inter hcH).isPreconnected
  have hB : IsPreconnected ({z : ℂ | z.im < 0} ∩ H) :=
    ((convex_halfSpace_im_lt 0).inter hcH).isPreconnected
  have hC : IsPreconnected ({z : ℂ | z.re < 1} ∩ H) :=
    ((convex_halfSpace_re_lt 1).inter hcH).isPreconnected
  have hD : IsPreconnected ({z : ℂ | 1 < z.re} ∩ H) :=
    ((convex_halfSpace_re_gt 1).inter hcH).isPreconnected
  have hUconn : IsPreconnected U := by
    have hUV : U = (({z : ℂ | 0 < z.im} ∩ H) ∪ ({z : ℂ | z.re < 1} ∩ H)
          ∪ ({z : ℂ | z.im < 0} ∩ H)) ∪ ({z : ℂ | 1 < z.re} ∩ H) := by
      ext z
      simp only [hUdef, hHdef, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hre, hne⟩
        rcases lt_trichotomy z.im 0 with him | him | him
        · exact .inl (.inr ⟨him, hre⟩)
        · rcases lt_trichotomy z.re 1 with hlt | heq | hgt
          · exact .inl (.inl (.inr ⟨hlt, hre⟩))
          · exact absurd (Complex.ext (heq.trans Complex.one_re.symm)
              (him.trans Complex.one_im.symm)) hne
          · exact .inr ⟨hgt, hre⟩
        · exact .inl (.inl (.inl ⟨him, hre⟩))
      · rintro (((⟨h, hre⟩ | ⟨h, hre⟩) | ⟨h, hre⟩) | ⟨h, hre⟩) <;>
          exact ⟨hre, by rintro rfl; simp only [Complex.one_im, Complex.one_re] at h; linarith⟩
    -- glue the four convex pieces at `I`, `-I` and `2 + I`
    have mem : ∀ z : ℂ, ∀ S : Set ℂ, z ∈ S → 0 ≤ z.re → z ∈ S ∩ H := fun _ _ h hz ↦ ⟨h, hmH _ hz⟩
    rw [hUV]
    exact ((hA.union Complex.I (mem _ _ (by simp) (by simp)) (mem _ _ (by simp) (by simp))
        hC).union (-Complex.I) (.inr (mem _ _ (by simp) (by simp)))
        (mem _ _ (by simp) (by simp)) hB).union
      (2 + Complex.I) (.inl (.inl (mem _ _ (by simp) (by simp))))
      (mem _ _ (by simp) (by simp)) hD
  have hagree : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (fun z ↦ zetaEMExpansion z M N) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    have hz1 : 1 < z.re := hz
    rw [riemannZeta_eq_of_one_lt_re z hz1 M N hN]
    simp only [zetaEMExpansion]
    rw [Complex.eulerMaclaurinRemainderIoi_succ_eq z M N hN (by linarith : -(2 * M : ℝ) < z.re)]
    ring
  exact hζ.eqOn_of_preconnected_of_eventuallyEq hE hUconn ⟨hmH _ (by simp), by simp⟩ hagree
    ⟨hs, hs1⟩

/-- The Euler–Maclaurin expansion of `ζ` as approximant plus remainder. For `1 ≤ N`,
`Re s > -(2M+1)` and `s ≠ 1`, `riemannZeta s = zetaApproximant s M N + zetaRemainder s M N`. -/
theorem riemannZeta_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaApproximant s M N + zetaRemainder s M N := by
  rw [riemannZeta_eq s M N hN hs hs1, zetaEMExpansion_eq_approximant_add_remainder]

/-- The first-order Euler–Maclaurin representation of `ζ`. For `0 < Re s` and `s ≠ 1`,
`ζ(s) = 1/(s-1) + 1/2 + R₁(s)`, with the order-`1` improper remainder
`R₁(s) = Complex.eulerMaclaurinRemainderIoi 1 (y ↦ y^{-s}) 1`. -/
theorem riemannZeta_eq_order_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2
      + Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (1 : ℝ) := by
  have h2 := Complex.eulerMaclaurinRemainderIoi_succ_eq s 0 1 le_rfl (by push_cast; linarith)
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow] at h2
  rw [riemannZeta_eq s 0 1 le_rfl (by push_cast; linarith) hs1, zetaEMExpansion]
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow, Finset.Ico_self,
    Finset.sum_empty, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by lia)]
  linear_combination -h2

/-- `Re ζ(x) < 0` for real `x ∈ (0, 1)`. -/
theorem riemannZeta_ofReal_re_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs1 : (x : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  rw [riemannZeta_eq_order_one (by simpa using hx0) hs1, Complex.add_re, Complex.add_re,
    show (1 / ((x : ℂ) - 1)).re = 1 / (x - 1) from by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_one,
        ← Complex.ofReal_div, Complex.ofReal_re],
    show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
  have hRre := (Complex.re_le_norm _).trans
    (Complex.norm_eulerMaclaurinRemainderIoi_one_ofReal_le hx0)
  have hlt : 1 / (x - 1) < -1 := by
    rw [div_lt_iff_of_neg (show x - 1 < 0 by linarith)]; linarith
  linarith
