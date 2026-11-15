/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.ArgZeta.ShiftIdentity
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Lehman's explicit bound §3: the real-`ζ` lower bound and the Dirichlet/digamma constants

The explicit digamma-remainder constants and the Dirichlet sum `D(σ) = ∑ₙ Λ(n) n^{-σ} =
-ζ'/ζ(σ)`, together with the real-axis lower bounds on `ζ` they rely on, and the explicit log-`t`
witnesses `C_ψ` for the shifted pairing sum that they yield.

## Main results

- `one_div_sub_one_le_riemannZeta_ofReal` (`lem:le_zeta_pole_lower`), `riemannZeta_ofReal_ge_sharp`
  (`lem:ls_zeta_lower_sharp`): lower bounds for `ζ` on the real axis.
- `norm_digammaRemainderIoi_one_le` (`lem:le_digamma_const`): the order-`1` digamma remainder.
- `tsum_vonMangoldt_norm_le` (`lem:le_dirichlet_bound`), `tsum_vonMangoldt_norm_le_124`,
  `tsum_vonMangoldt_norm_le_124_sharp` (`lem:ls_dirichlet_sharp`): explicit Dirichlet-sum bounds
  at `σ = 103/100` and `σ = 124/100`.
- `tsum_re_inv_riemannXiZeros_sub_le_explicit` (`lem:le_zeta_sum_explicit`), `..._tight`,
  `..._tight_sharp` (`lem:ls_Cpsi`, `lem:ls_Cpsi_sharp`): the log-`t` witnesses.
-/
@[expose] public section


open Complex Filter Topology Function Set


/-- For real `σ > 1`, the real `p`-series `n ↦ ((n:ℝ)+1)^{-σ}` is summable and sums to the real
`ζ(σ)`. -/
private lemma summable_and_riemannZeta_ofReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ (-σ)) ∧
      riemannZeta (σ : ℂ) = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  refine ⟨?_, ?_⟩
  · refine ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hneg)).congr (fun n ↦ ?_)
    rw [Nat.cast_add, Nat.cast_one]
  · rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hσ), Complex.ofReal_tsum]
    refine tsum_congr (fun n ↦ ?_)
    have hbase : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hbase, Complex.ofReal_inv, Complex.ofReal_cpow hbase, one_div]
    push_cast
    ring

/-- The shifted `p`-series Riemann-sum window: for real `σ > 1` and a shift `k`, the tail
integral `∫_{k+1}^{∞} x^{-σ} dx = (k+1)^{1-σ}/(σ-1)` is bounded by the shifted `p`-series
`∑_{n} (n+k+1)^{-σ}`. -/
private lemma integral_Ioi_rpow_le_tsum_shift {σ : ℝ} (hσ : 1 < σ) (k : ℕ) :
    ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) ≤ ∑' n : ℕ, (((n + k : ℕ) : ℝ) + 1) ^ (-σ) := by
  have hneg : (-σ : ℝ) < -1 := by linarith
  have hb : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  obtain ⟨hsum, -⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  have hintval : ∫ x in Set.Ioi ((k : ℝ) + 1), x ^ (-σ) = ((k : ℝ) + 1) ^ (1 - σ) / (σ - 1) := by
    rw [integral_Ioi_rpow_of_lt hneg hb, show (-σ + 1 : ℝ) = -(σ - 1) by ring, neg_div_neg_eq,
      show (-(σ - 1) : ℝ) = 1 - σ by ring]
  rw [← hintval]
  refine Real.integral_Ioi_le_tsum_of_window k hsum (integrableOn_Ioi_rpow_of_lt hneg hb)
    fun N ↦ (Real.antitoneOn_rpow_neg_Icc (a := (k : ℝ) + 1) (b := (k : ℝ) + 1 + (N : ℝ))
      (by linarith) hb).integral_le_sum.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
  show ((k : ℝ) + 1 + (i : ℝ)) ^ (-σ) = a (i + k)
  simp only [ha]; congr 1; push_cast; ring

/-- Lower bound for `ζ` on the real axis (`lem:le_zeta_pole_lower`). For real `σ > 1`,
`1 / (σ - 1) ≤ Re ζ(σ)`. -/
theorem one_div_sub_one_le_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨-, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  rw [hzeq, Complex.ofReal_re]
  simpa using integral_Ioi_rpow_le_tsum_shift hσ 0

/-- Sharp lower bound for `ζ` on the real axis (`lem:ls_zeta_lower_sharp`). For real `σ > 1`,
`ζ(σ) ≥ 1 + 2^{-σ} + 3^{-σ} + 4^{1-σ}/(σ-1)`. This sharpens
`one_div_sub_one_le_riemannZeta_ofReal`, which drops the first three terms. -/
theorem riemannZeta_ofReal_ge_sharp {σ : ℝ} (hσ : 1 < σ) :
    1 + 2 ^ (-σ) + 3 ^ (-σ) + 4 ^ (1 - σ) / (σ - 1) ≤ (riemannZeta (σ : ℂ)).re := by
  obtain ⟨hsum, hzeq⟩ := summable_and_riemannZeta_ofReal_eq_tsum hσ
  set a : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ (-σ) with ha
  rw [hzeq, Complex.ofReal_re]
  -- the `k = 3` Riemann-sum window: `∫_{Ioi 4} x^{-σ} = 4^{1-σ}/(σ-1) ≤ ∑_{n≥4} n^{-σ}`
  have htail : (4 : ℝ) ^ (1 - σ) / (σ - 1) ≤ ∑' n, a (n + 3) := by
    have h := integral_Ioi_rpow_le_tsum_shift hσ 3
    rw [show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
    simpa [ha] using h
  -- split off the first three terms `a 0 = 1`, `a 1 = 2^{-σ}`, `a 2 = 3^{-σ}`
  have hfirst : (∑ i ∈ Finset.range 3, a i) = 1 + 2 ^ (-σ) + 3 ^ (-σ) := by
    simp only [ha, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.one_rpow]
  rw [(hsum.sum_add_tsum_nat_add 3).symm, hfirst]
  linarith [htail]

/-! ## §3: the explicit digamma remainder and the Dirichlet sum

The dominant term `C_ψ` of `lem:ll_zeta_sum` is the Dirichlet sum
`D(σ) = ∑ₙ Λ(n) n^{-σ} = -ζ'/ζ(σ)`, pinned explicitly at the working abscissae `σ = 103/100`
(`d = 53/100`) and `σ = 124/100` (`d = 74/100`). -/

/-! ### The explicit digamma-remainder constants

The order-`1` improper digamma remainder `digammaRemainderIoi s 1` equals `ψ(s) - Log s + (2s)⁻¹`
up to sign, and is pinned here with a constant independent of `Re s`. -/

section Digamma
open Complex.Stirling MeasureTheory
open scoped Nat Real

/-- Order-`1`-to-order-`2` digamma-remainder recurrence (`lem:le_digamma_recurrence`). For
`Re s > 0`, `digammaRemainderIoi s 1 - digammaRemainderIoi s 2 = B₂/2 · s⁻²` (with `B₂ = 1/6`, so
the coefficient has modulus `1/12`). -/
theorem digammaRemainderIoi_one_sub_two {s : ℂ} (hs : 0 < s.re) :
    digammaRemainderIoi s 1 - digammaRemainderIoi s 2
      = (bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (s + (y : ℂ))⁻¹ with hf
  -- `s + x ≠ 0` for every nonnegative real `x`.
  have hne : ∀ x : ℝ, 0 ≤ x → s + (x : ℂ) ≠ 0 := fun x hx h ↦ by
    have hre : (s + (x : ℂ)).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at hre; linarith
  have hsub : ∀ N : ℕ,
      Set.uIcc ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) ⊆ {y : ℝ | s + (y : ℂ) ≠ 0} := by
    intro N
    rw [Int.cast_zero, zero_add, Set.uIcc_of_le (by positivity)]
    exact fun y hy ↦ hne y hy.1
  -- Closed form of the first derivative at the (nonnegative) endpoints.
  have hid1 : ∀ x : ℝ, 0 ≤ x → iteratedDeriv 1 f x = -(s + (x : ℂ)) ^ (-(2 : ℤ)) := by
    intro x hx
    rw [hf, iteratedDeriv_inv_add_ofReal s 1 (hne x hx)]
    norm_num
  -- The finite Euler–Maclaurin recurrence at truncation `N`.
  have hfin : ∀ N : ℕ,
      eulerMaclaurinRemainder 1 f 0 (N : ℝ) - eulerMaclaurinRemainder 2 f 0 (N : ℝ)
        = (bernoulli 2 : ℂ) / 2 * (s ^ (-(2 : ℤ)) - (s + (N : ℂ)) ^ (-(2 : ℤ))) := by
    intro N
    have hderiv : ∀ q, q < 2 → ∀ x ∈ {y : ℝ | s + (y : ℂ) ≠ 0},
        HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
      fun q _ x hx ↦ hasDerivAt_iteratedDeriv_inv_add_ofReal s q hx
    have hint : ∀ q, 0 < q → q ≤ 2 →
        IntervalIntegrable (iteratedDeriv q f) volume ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) := by
      intro q _ _
      rw [Int.cast_zero, zero_add]
      exact intervalIntegrable_iteratedDeriv_inv_add_ofReal s hs q le_rfl (by positivity)
    have E1 := Complex.sum_eq (f := f) 0 (N := N) (p := 1) one_pos
      (fun q _ x hx ↦ hderiv q (by lia) x (hsub N hx)) (fun q hq0 hq ↦ hint q hq0 (by lia))
    have E2 := Complex.sum_eq (f := f) 0 (N := N) (p := 2) two_pos
      (fun q hq x hx ↦ hderiv q hq x (hsub N hx)) hint
    simp only [Int.cast_zero, zero_add] at E1 E2
    rw [show (1 : ℕ) / 2 + 1 = 1 from rfl, Finset.Ico_self, Finset.sum_empty] at E1
    -- Evaluate the single-term boundary sum in the order-`2` expansion.
    rw [show (Finset.Ico 1 (2 / 2 + 1) : Finset ℕ) = {1} from by
        ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; lia,
      Finset.sum_singleton, show (2 * 1 - 1 : ℕ) = 1 from rfl, show (2 * 1 : ℕ) = 2 from rfl,
      hid1 (N : ℝ) (by positivity), hid1 0 le_rfl,
      show ((2 : ℕ)! : ℝ) = 2 from by norm_num [Nat.factorial]] at E2
    push_cast at E2
    simp only [add_zero] at E2
    linear_combination E2 - E1
  -- Pass to the improper integral: `remℂ p f 0 N → digammaRemainderIoi s p`.
  have hlimR : ∀ p : ℕ, 1 ≤ p →
      Tendsto (fun N : ℕ ↦ eulerMaclaurinRemainder p f 0 (N : ℝ)) atTop
        (𝓝 (digammaRemainderIoi s p)) := by
    intro p hp
    simp only [Complex.eulerMaclaurinRemainder_eq, digammaRemainderIoi, hf]
    exact (intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add s hs p hp)
      tendsto_natCast_atTop_atTop).const_mul _
  -- `(s + N)⁻² → 0`.
  have hz0 : Tendsto (fun N : ℕ ↦ (s + (N : ℂ)) ^ (-(2 : ℤ))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ ↦ ((s + (N : ℂ))⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_add_natCast_atTop (s := s)).pow 2
    exact hpow.congr fun N ↦ by
      rw [show (-(2 : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, inv_pow]
  -- Combine: uniqueness of limits along the finite recurrence.
  have hL := (hlimR 1 le_rfl).sub (hlimR 2 (by norm_num))
  have hR : Tendsto (fun N : ℕ ↦ (bernoulli 2 : ℂ) / 2
      * (s ^ (-(2 : ℤ)) - (s + (N : ℂ)) ^ (-(2 : ℤ)))) atTop
      (𝓝 ((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)))) := by
    simpa using (tendsto_const_nhds.sub hz0).const_mul ((bernoulli 2 : ℂ) / 2)
  rw [funext hfin] at hL
  exact tendsto_nhds_unique hL hR

/-- Explicit order-`1` digamma-remainder bound (`lem:le_digamma_const`). For `Re s > 0`,
`‖digammaRemainderIoi s 1‖ ≤ (1/π + 1/12) · ‖s‖⁻²`. -/
theorem norm_digammaRemainderIoi_one_le {s : ℂ} (hs : 0 < s.re) :
    ‖digammaRemainderIoi s 1‖ ≤ (1 / π + 1 / 12) * ‖s‖ ^ (-(2 : ℤ)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hR2' : ‖digammaRemainderIoi s 2‖ ≤ 1 / π * ‖s‖ ^ (-(2 : ℤ)) := by
    refine (norm_digammaRemainderIoi_le' s hs 2 (by norm_num)).trans (le_of_eq ?_)
    rw [show ((2 : ℕ)! : ℝ) = 2 from by norm_num [Nat.factorial], show (2 - 1 : ℕ) = 1 from rfl,
      pow_one, show (-((2 : ℕ) : ℤ)) = -(2 : ℤ) from by norm_num]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  calc ‖digammaRemainderIoi s 1‖
      = ‖digammaRemainderIoi s 2 + (bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ))‖ := by
        rw [show digammaRemainderIoi s 1
          = digammaRemainderIoi s 2 + (bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)) from by
            linear_combination digammaRemainderIoi_one_sub_two hs]
    _ ≤ ‖digammaRemainderIoi s 2‖ + 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_mul, norm_zpow, bernoulli_two, norm_div, Complex.norm_ratCast]; norm_num
    _ ≤ 1 / π * ‖s‖ ^ (-(2 : ℤ)) + 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) := by gcongr
    _ = (1 / π + 1 / 12) * ‖s‖ ^ (-(2 : ℤ)) := by ring

end Digamma

open scoped LSeries.notation
open ArithmeticFunction
open scoped Real

/-- The antiderivative `-x^{1-σ}(log x/(σ-1) + 1/(σ-1)²)` of `x ↦ (log x) x^{-σ}`. -/
private noncomputable def negZetaDerivAntideriv (σ x : ℝ) : ℝ :=
  -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x) - (1 / (σ - 1) ^ 2) * x ^ (1 - σ)

/-- `negZetaDerivAntideriv σ` is an antiderivative of `x ↦ (log x) x^{-σ}` on `(0, ∞)`. -/
private lemma hasDerivAt_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (negZetaDerivAntideriv σ) (Real.log x * x ^ (-σ)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
  have hA : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ)) ((1 - σ) * x ^ (1 - σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx0)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h1 : HasDerivAt (fun y : ℝ ↦ y ^ (1 - σ) * Real.log y)
      ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹) x := hA.mul hlog
  have p1 : x ^ (1 - σ - 1) = x ^ (-σ) := by rw [show (1 - σ - 1) = -σ by ring]
  have p2 : x ^ (1 - σ) * x⁻¹ = x ^ (-σ) := by
    rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hx,
      show (1 - σ + -1 : ℝ) = -σ by ring]
  rw [show Real.log x * x ^ (-σ)
      = -(1 / (σ - 1)) * ((1 - σ) * x ^ (1 - σ - 1) * Real.log x + x ^ (1 - σ) * x⁻¹)
        - 1 / (σ - 1) ^ 2 * ((1 - σ) * x ^ (1 - σ - 1)) from by rw [p1, p2]; field_simp; ring]
  exact (h1.const_mul (-(1 / (σ - 1)))).sub (hA.const_mul (1 / (σ - 1) ^ 2))

/-- The antiderivative tends to `0` at `+∞`, since `1 - σ < 0`. -/
private lemma tendsto_negZetaDerivAntideriv {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (negZetaDerivAntideriv σ) atTop (𝓝 0) := by
  have hc : (0 : ℝ) < σ - 1 := by linarith
  have h1 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ)) atTop (𝓝 0) := by
    simpa [show -(σ - 1) = 1 - σ by ring] using tendsto_rpow_neg_atTop hc
  have h2 : Tendsto (fun x : ℝ ↦ x ^ (1 - σ) * Real.log x) atTop (𝓝 0) := by
    refine ((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show (1 - σ) = -(σ - 1) by ring, Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]
  have hcomb := (h2.const_mul (-(1 / (σ - 1)))).sub (h1.const_mul (1 / (σ - 1) ^ 2))
  rw [show (fun x : ℝ ↦ -(1 / (σ - 1)) * (x ^ (1 - σ) * Real.log x)
    - 1 / (σ - 1) ^ 2 * x ^ (1 - σ)) = negZetaDerivAntideriv σ from rfl] at hcomb
  simpa using hcomb

/-- Explicit bound on `-ζ'` on the real axis (`lem:le_neg_deriv_zeta`). For real `σ > 1`,
`-ζ'(σ) ≤ (log 2) 2^{-σ} + (log 3) 3^{-σ} + 3^{1-σ}(log 3/(σ-1) + 1/(σ-1)²)`. -/
theorem neg_deriv_riemannZeta_ofReal_le {σ : ℝ} (hσ : 1 < σ) :
    (- deriv riemannZeta (σ : ℂ)).re ≤
      Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
        + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
  set f : ℝ → ℝ := fun x ↦ Real.log x * x ^ (-σ) with hf
  set b : ℕ → ℝ := fun n ↦ Real.log n * (n : ℝ) ^ (-σ) with hb
  -- `(-ζ'(σ)).re = ∑' n, (log n) n^{-σ}`, via `deriv (LSeries 1) = -LSeries (log · 1)`.
  have habs : LSeries.abscissaOfAbsConv 1 < ((σ : ℂ)).re := by
    rw [LSeries.abscissaOfAbsConv_one, Complex.ofReal_re]; exact_mod_cast hσ
  have hEv : riemannZeta =ᶠ[𝓝 (σ : ℂ)] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < ((σ : ℂ)).re by rwa [Complex.ofReal_re])] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have h1 : HasSum b (- deriv riemannZeta (σ : ℂ)).re := by
    have h0 : HasSum (LSeries.term (LSeries.logMul 1) (σ : ℂ)) (- deriv riemannZeta (σ : ℂ)) := by
      rw [hEv.deriv_eq, LSeries_deriv habs, neg_neg]
      exact (LSeriesSummable_logMul_of_lt_re habs).hasSum
    refine (Complex.hasSum_re h0).congr_fun fun n ↦ Eq.symm ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hb, LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [LSeries.term_of_ne_zero hn]
      simp only [hb, LSeries.logMul, Pi.one_apply, mul_one]
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_log hnpos.le, ← Complex.ofReal_cpow hnpos.le,
          ← Complex.ofReal_div, Complex.ofReal_re, Real.rpow_neg hnpos.le, div_eq_mul_inv]
  have hbsum : Summable b := h1.summable
  rw [← h1.tsum_eq]
  -- Integral test: `f` is antitone on `[3, ∞)`, since `log x > 1` there.
  have hlog3 : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hderivf : ∀ {x : ℝ}, 0 < x →
      HasDerivAt f (x⁻¹ * x ^ (-σ) + Real.log x * (-σ * x ^ (-σ - 1))) x := fun hx ↦
    (Real.hasDerivAt_log hx.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
  have hdf : ∀ x ∈ Set.Ici (3 : ℝ), DifferentiableAt ℝ f x := fun x hx ↦
    (hderivf (by simp only [Set.mem_Ici] at hx; linarith)).differentiableAt
  have hderiv_np : ∀ x ∈ Set.Ioi (3 : ℝ), deriv f x ≤ 0 := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : (1 : ℝ) < Real.log x := hlog3.trans_le (Real.log_le_log (by norm_num) hx.le)
    rw [(hderivf hxpos).deriv, show x⁻¹ * x ^ (-σ) = x ^ (-σ - 1) by
      rw [show x⁻¹ = x ^ (-1 : ℝ) from (Real.rpow_neg_one x).symm, ← Real.rpow_add hxpos,
        show (-1 + -σ : ℝ) = -σ - 1 by ring]]
    nlinarith [Real.rpow_pos_of_pos hxpos (-σ - 1), hlogx, hσ,
      mul_nonneg (by linarith : (0 : ℝ) ≤ σ - 1) (by linarith : (0 : ℝ) ≤ Real.log x - 1)]
  have hanti : AntitoneOn f (Set.Ici (3 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 3)
      (fun x hx ↦ (hdf x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ (hdf x (interior_subset hx)).differentiableWithinAt) ?_
    rw [interior_Ici]; exact hderiv_np
  -- FTC on `[3, ∞)` with the antiderivative `negZetaDerivAntideriv σ`.
  have hcont : ContinuousWithinAt (negZetaDerivAntideriv σ) (Set.Ici 3) 3 :=
    (hasDerivAt_negZetaDerivAntideriv hσ (by norm_num)).continuousAt.continuousWithinAt
  have hderivF : ∀ x ∈ Set.Ioi (3 : ℝ), HasDerivAt (negZetaDerivAntideriv σ) (f x) x :=
    fun x hx ↦ hasDerivAt_negZetaDerivAntideriv hσ (by simp only [Set.mem_Ioi] at hx; linarith)
  have hfpos : ∀ x ∈ Set.Ioi (3 : ℝ), 0 ≤ f x := fun x hx ↦
    mul_nonneg (Real.log_nonneg (by simp only [Set.mem_Ioi] at hx; linarith))
      (Real.rpow_nonneg (by simp only [Set.mem_Ioi] at hx; linarith) _)
  have hlim := tendsto_negZetaDerivAntideriv hσ
  have htail : ∑' k, b (k + 4) ≤ (0 : ℝ) - negZetaDerivAntideriv σ 3 := by
    refine (Real.tsum_le_integral_Ioi_of_window 4 hbsum
        (MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderivF hfpos hlim)
        (fun N ↦ le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
          (hanti.mono Set.Icc_subset_Ici_self).sum_le_integral)).trans_eq
      (MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderivF hfpos hlim)
    simp only [hb, hf]
    rw [show ((i + 4 : ℕ) : ℝ) = 3 + ((i + 1 : ℕ) : ℝ) by push_cast; ring]
  have hfirst : (∑ i ∈ Finset.range 4, b i) = Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ) := by
    simp only [hb, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num [Real.log_zero]
  have hFval : (0 : ℝ) - negZetaDerivAntideriv σ 3
      = 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) := by
    simp only [negZetaDerivAntideriv]; ring
  rw [(hbsum.sum_add_tsum_nat_add 4).symm, hfirst]
  linarith [hFval ▸ htail]

/-- `log 3 ≤ 1099/1000`. -/
private lemma log_three_le : Real.log 3 ≤ 1099 / 1000 := by
  linarith [Real.log_three_lt_d9]

/-- Uniform first-two-term bounds for the Dirichlet numerator: for `σ > 1`,
`log 2 · 2^{-σ} ≤ 7/10` and `log 3 · 3^{-σ} ≤ 6/5`. -/
private lemma log_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    Real.log 2 * (2 : ℝ) ^ (-σ) ≤ 7 / 10 ∧ Real.log 3 * (3 : ℝ) ^ (-σ) ≤ 6 / 5 := by
  have e2 : (2 : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have e3 : (3 : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  exact ⟨by nlinarith [Real.log_two_lt_d9, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2), e2,
            Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-σ)],
         by nlinarith [log_three_le, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3), e3,
            Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-σ)]⟩

/-- The numerical step of `tsum_vonMangoldt_norm_le`: at `σ = 103/100` the explicit bound of
`neg_deriv_riemannZeta_ofReal_le` times `σ - 1` is at most `35`. -/
private lemma explicit_neg_deriv_bound_mul_le {σ : ℝ} (hσdef : σ = 103 / 100) :
    (Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
      + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2)) * (σ - 1) ≤ 35 := by
  have hσ : 1 < σ := by rw [hσdef]; norm_num
  set E : ℝ := Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
      + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) with hEdef
  obtain ⟨ht1, ht2⟩ := log_rpow_neg_le hσ
  have hinner_nn : 0 ≤ Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2 := by rw [hσdef]; positivity
  have ht3 : 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2)
      ≤ Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2 :=
    mul_le_of_le_one_left hinner_nn
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by rw [hσdef]; norm_num))
  have hinnerbd : Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2 ≤ 40 + 10000 / 9 := by
    rw [hσdef, show Real.log 3 / (103 / 100 - 1 : ℝ) + 1 / (103 / 100 - 1 : ℝ) ^ 2
      = Real.log 3 * (100 / 3) + 10000 / 9 by ring]
    linarith [log_three_le]
  -- `E ≤ 7/10 + 6/5 + (40 + 10000/9) = 103771/90`, and `(103771/90) * (3/100) < 35`.
  have hEbig : E ≤ 103771 / 90 := by rw [hEdef]; linarith [ht1, ht2, ht3, hinnerbd]
  rw [show σ - 1 = 3 / 100 by rw [hσdef]; norm_num]
  linarith [hEbig]

/-- The Dirichlet-sum modulus as `(-ζ')/ζ` at a real abscissa: for real `σ > 1`,
`∑ₙ ‖Λ(n) n^{-σ}‖ = (-ζ'(σ)).re · (ζ(σ).re)⁻¹`, with `ζ(σ).re > 0` and `(-ζ'(σ)).re ≥ 0`. -/
private lemma tsum_norm_term_vonMangoldt_eq_and_pos {σ : ℝ} (hσ : 1 < σ) :
    ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖
        = (- deriv riemannZeta (σ : ℂ)).re * ((riemannZeta (σ : ℂ)).re)⁻¹ ∧
      0 < (riemannZeta (σ : ℂ)).re ∧ 0 ≤ (- deriv riemannZeta (σ : ℂ)).re := by
  set s : ℂ := (σ : ℂ) with hsdef
  have hs : 1 < s.re := by rw [hsdef, Complex.ofReal_re]; exact hσ
  -- each term is a nonnegative real, so `∑ₙ ‖·‖ = Re (∑ₙ ·) = Re (-ζ'/ζ)`
  have hnorm_re : ∀ n : ℕ, (LSeries.term ↗Λ s n).re = ‖LSeries.term ↗Λ s n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hnpos : 0 < (n : ℝ) := by positivity
      rw [show LSeries.term ↗Λ s n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) from by
            rw [LSeries.term_of_ne_zero hn, hsdef,
              show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
              ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_div],
          Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg hnpos.le σ))]
  have hD : ∑' n, ‖LSeries.term ↗Λ s n‖ = (LSeries ↗Λ s).re :=
    ((Complex.hasSum_re (LSeriesSummable_vonMangoldt hs).hasSum).congr_fun
      (fun n ↦ (hnorm_re n).symm)).tsum_eq
  -- `ζ(σ)` is real and positive
  have hterm : ∀ n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ s = (((1 / ((n : ℝ) + 1) ^ σ : ℝ)) : ℂ) := by
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one, hsdef, Complex.ofReal_cpow (by positivity)]
    push_cast; ring
  have hζim : (riemannZeta s).im = 0 := by
    rw [hsdef, zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; exact hσ),
        tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_im]
  have hσ1pos : (0 : ℝ) < σ - 1 := by linarith
  have hζpos : 0 < (riemannZeta s).re :=
    lt_of_lt_of_le (by positivity) (one_div_sub_one_le_riemannZeta_ofReal hσ)
  set r : ℝ := (riemannZeta s).re with hrdef
  have hζeq : riemannZeta s = (r : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im, hζim])
  have hDeq : ∑' n, ‖LSeries.term ↗Λ s n‖ = (- deriv riemannZeta s).re * r⁻¹ := by
    rw [hD, LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hζeq, div_eq_mul_inv,
      ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  refine ⟨hDeq, hζpos, ?_⟩
  nlinarith [hDeq ▸ tsum_nonneg (fun n ↦ norm_nonneg (LSeries.term ↗Λ s n)), inv_pos.mpr hζpos]

/-- The explicit Dirichlet-sum majorant at a real abscissa: for real `σ > 1`,
`∑ₙ ‖Λ(n) n^{-σ}‖` is at most the closed form of `neg_deriv_riemannZeta_ofReal_le` times
`σ - 1`. -/
private lemma tsum_norm_term_vonMangoldt_le_mul {σ : ℝ} (hσ : 1 < σ) :
    ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖
      ≤ (Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
        + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2)) * (σ - 1) := by
  obtain ⟨hDeq, hζpos, hAnn⟩ := tsum_norm_term_vonMangoldt_eq_and_pos hσ
  have hσ1pos : (0 : ℝ) < σ - 1 := by linarith
  set A : ℝ := (- deriv riemannZeta (σ : ℂ)).re with hAdef
  set r : ℝ := (riemannZeta (σ : ℂ)).re with hrdef
  set E : ℝ := Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
      + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) with hEdef
  have hAle : A ≤ E := neg_deriv_riemannZeta_ofReal_le hσ
  -- `ζ(σ) ≥ 1/(σ-1)` inverts to `(ζ(σ).re)⁻¹ ≤ σ - 1`
  have hinvle : r⁻¹ ≤ σ - 1 := (inv_le_comm₀ hζpos hσ1pos).mpr (by
    rw [← one_div]; exact one_div_sub_one_le_riemannZeta_ofReal hσ)
  rw [hDeq]
  exact mul_le_mul hAle hinvle (inv_pos.mpr hζpos).le (hAnn.trans hAle)

/-- Explicit Dirichlet-sum bound (`lem:le_dirichlet_bound`). At the abscissa `σ = 103/100`
(`= ½ + d`, `d = 53/100`), `D(σ) = ∑ₙ ‖Λ(n) n^{-σ}‖ ≤ 35`. -/
theorem tsum_vonMangoldt_norm_le :
    ∑' n, ‖LSeries.term ↗Λ ((103 / 100 : ℝ) : ℂ) n‖ ≤ 35 :=
  (tsum_norm_term_vonMangoldt_le_mul (σ := 103 / 100) (by norm_num)).trans
    (explicit_neg_deriv_bound_mul_le rfl)

/-- The `25`th power of `x^e` collapses to the rational `(x^k)⁻¹` whenever `e·25 = -k`
(`0 ≤ x`). -/
private lemma rpow_pow_25 {x e : ℝ} (hx : 0 ≤ x) {k : ℕ} (he : e * (25 : ℕ) = -(k : ℕ)) :
    (x ^ e) ^ (25 : ℕ) = (x ^ k)⁻¹ := by
  rw [← Real.rpow_natCast (x ^ e) 25, ← Real.rpow_mul hx, he, Real.rpow_neg hx, Real.rpow_natCast]

/-- `3^{1-124/100} = 3^{-6/25} ≤ 9/10`. -/
private lemma rpow_three_one_sub_le : (3 : ℝ) ^ (1 - 124 / 100 : ℝ) ≤ 9 / 10 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)

/-- The near-pole factor at `σ = 124/100`: `log 3/(σ-1) + 1/(σ-1)² ≤ 439/20`. -/
private lemma inner_pole_bound_124 :
    Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2 ≤ 439 / 20 := by
  rw [show Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2
    = Real.log 3 * (25 / 6) + 625 / 36 by ring]
  linarith [log_three_le]

/-- The numerical step at `σ = 124/100` (`= ½ + d`, `d = 74/100`): the explicit majorant of
`neg_deriv_riemannZeta_ofReal_le` times `σ - 1` is at most `28/5`. -/
private lemma explicit_neg_deriv_bound_mul_le_124 {σ : ℝ} (hσdef : σ = 124 / 100) :
    (Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
      + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2)) * (σ - 1) ≤ 28 / 5 := by
  have hσ : 1 < σ := by rw [hσdef]; norm_num
  set E : ℝ := Real.log 2 * 2 ^ (-σ) + Real.log 3 * 3 ^ (-σ)
      + 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) with hEdef
  obtain ⟨ht1, ht2⟩ := log_rpow_neg_le hσ
  have hinner_nn : 0 ≤ Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2 := by rw [hσdef]; positivity
  have ht3 : 3 ^ (1 - σ) * (Real.log 3 / (σ - 1) + 1 / (σ - 1) ^ 2) ≤ (9 / 10) * (439 / 20) :=
    mul_le_mul (by rw [hσdef]; exact rpow_three_one_sub_le)
      (by rw [hσdef]; exact inner_pole_bound_124) hinner_nn (by norm_num)
  have hEbig : E ≤ 7 / 10 + 6 / 5 + (9 / 10) * (439 / 20) := by
    rw [hEdef]; linarith [ht1, ht2, ht3]
  rw [show σ - 1 = 6 / 25 by rw [hσdef]; norm_num]
  linarith [hEbig]

/-- Explicit Dirichlet-sum bound at `σ = 124/100` (`= ½ + d`, `d = 74/100`): `D(σ) ≤ 28/5`.
The deeper abscissa, further from the pole at `σ = 1`, collapses the `35` of
`tsum_vonMangoldt_norm_le`. -/
theorem tsum_vonMangoldt_norm_le_124 :
    ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ 28 / 5 :=
  (tsum_norm_term_vonMangoldt_le_mul (σ := 124 / 100) (by norm_num)).trans
    (explicit_neg_deriv_bound_mul_le_124 rfl)

/-! ### The sharp Dirichlet constant at `σ = 124/100` (`sec:ls_five`)

The sharp bound `D(124/100) ≤ 379/100` (`tsum_vonMangoldt_norm_le_124_sharp`), improving the
`28/5` of `tsum_vonMangoldt_norm_le_124`. It feeds the tight `C_ψ ≤ 319/100`, hence `A ≤ 5`. -/

/-- `42/100 ≤ 2^{-124/100}` (`(42/100)^{25} ≤ 2^{-31}`). -/
private lemma rpow_two_neg_124_ge : (42 / 100 : ℝ) ≤ (2 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)

/-- `1/4 ≤ 3^{-124/100}` (`(1/4)^{25} ≤ 3^{-31}`). -/
private lemma rpow_three_neg_124_ge : (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (-(124 / 100) : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)

/-- `71/100 ≤ 4^{1-124/100} = 4^{-6/25}` (`(71/100)^{25} ≤ 4^{-6}`). -/
private lemma rpow_four_one_sub_124_ge : (71 / 100 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)

/-- `2^{-124/100} ≤ 43/100` (`2^{-31} ≤ (43/100)^{25}`). -/
private lemma rpow_two_neg_124_le : (2 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 43 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)

/-- `3^{-124/100} ≤ 27/100` (`3^{-31} ≤ (27/100)^{25}`). -/
private lemma rpow_three_neg_124_le : (3 : ℝ) ^ (-(124 / 100) : ℝ) ≤ 27 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (-(124 / 100) : ℝ) * (25 : ℕ) = -(31 : ℕ) by push_cast; norm_num)]; norm_num)

/-- `3^{1-124/100} = 3^{-6/25} ≤ 77/100` (`3^{-6} ≤ (77/100)^{25}`), the tightening of
`rpow_three_one_sub_le` that brings `-ζ'(124/100)` down to `35/2`. -/
private lemma rpow_three_one_sub_124_le : (3 : ℝ) ^ (1 - 124 / 100 : ℝ) ≤ 77 / 100 :=
  le_of_pow_le_pow_left₀ (n := 25) (by norm_num) (by norm_num)
    (by rw [rpow_pow_25 (by norm_num)
      (show (1 - 124 / 100 : ℝ) * (25 : ℕ) = -(6 : ℕ) by push_cast; norm_num)]; norm_num)

/-- Sharp numerical value of `ζ` at `σ = 124/100` (`lem:ls_zeta_lower_sharp`, evaluated):
`ζ(124/100) ≥ 462/100`, versus the crude `1/(σ-1) = 25/6 ≈ 4.17`. -/
private lemma riemannZeta_ofReal_124_ge :
    (462 / 100 : ℝ) ≤ (riemannZeta ((124 / 100 : ℝ) : ℂ)).re := by
  have h4div : (1775 / 600 : ℝ) ≤ (4 : ℝ) ^ (1 - 124 / 100 : ℝ) / ((124 / 100 : ℝ) - 1) := by
    rw [show ((124 / 100 : ℝ) - 1) = 6 / 25 by norm_num,
      le_div_iff₀ (by norm_num : (0 : ℝ) < 6 / 25)]
    linarith [rpow_four_one_sub_124_ge]
  linarith [riemannZeta_ofReal_ge_sharp (σ := (124 / 100 : ℝ)) (by norm_num),
    rpow_two_neg_124_ge, rpow_three_neg_124_ge, h4div]

/-- Sharp numerator bound (`lem:ls_dirichlet_sharp`, numerator): `-ζ'(124/100) ≤ 35/2`. -/
private lemma neg_deriv_riemannZeta_124_le :
    (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re ≤ 35 / 2 := by
  refine (neg_deriv_riemannZeta_ofReal_le (by norm_num : (1 : ℝ) < 124 / 100)).trans ?_
  have ht1 : Real.log 2 * 2 ^ (-(124 / 100) : ℝ) ≤ (6932 / 10000) * (43 / 100) :=
    mul_le_mul (by linarith [Real.log_two_lt_d9]) rpow_two_neg_124_le
      (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht2 : Real.log 3 * 3 ^ (-(124 / 100) : ℝ) ≤ (1099 / 1000) * (27 / 100) :=
    mul_le_mul log_three_le rpow_three_neg_124_le (Real.rpow_nonneg (by norm_num) _) (by norm_num)
  have ht3 : 3 ^ (1 - 124 / 100 : ℝ)
      * (Real.log 3 / ((124 / 100 : ℝ) - 1) + 1 / ((124 / 100 : ℝ) - 1) ^ 2)
      ≤ (77 / 100) * (439 / 20) :=
    mul_le_mul rpow_three_one_sub_124_le inner_pole_bound_124 (by positivity) (by norm_num)
  linarith [ht1, ht2, ht3]

/-- Sharp explicit Dirichlet-sum bound at `σ = 124/100` (`lem:ls_dirichlet_sharp`):
`D(124/100) ≤ 379/100`, sharpening the `28/5` of `tsum_vonMangoldt_norm_le_124`. -/
theorem tsum_vonMangoldt_norm_le_124_sharp :
    ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ 379 / 100 := by
  obtain ⟨hDeq, hζpos, -⟩ :=
    tsum_norm_term_vonMangoldt_eq_and_pos (show (1 : ℝ) < 124 / 100 by norm_num)
  set A : ℝ := (- deriv riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hAdef
  set r : ℝ := (riemannZeta ((124 / 100 : ℝ) : ℂ)).re with hrdef
  have hinvle : r⁻¹ ≤ 100 / 462 := by
    rw [show (100 / 462 : ℝ) = (462 / 100)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) riemannZeta_ofReal_124_ge
  rw [hDeq]
  calc A * r⁻¹ ≤ (35 / 2) * (100 / 462) :=
        mul_le_mul neg_deriv_riemannZeta_124_le hinvle (inv_pos.mpr hζpos).le (by norm_num)
    _ ≤ 379 / 100 := by norm_num

/-- A positive imaginary part is a lower bound for the modulus: if `z.im = t > 0` then
`t ≤ ‖z‖`. -/
private lemma le_norm_of_im_eq {z : ℂ} {t : ℝ} (ht : 0 < t) (h : z.im = t) : t ≤ ‖z‖ := by
  simpa [h, abs_of_pos ht] using Complex.abs_im_le_norm z

/-- The digamma term on the shifted line (`lem:le_zeta_sum_explicit`, `lem:ls_Cpsi`). For
`1/2 < d ≤ 1` and `t ≥ 168π`, at `s_d = 1/2 + d + it` the digamma real part obeys
`Re ψ(s_d/2) ≤ log t - log 2 + 2/100`. -/
private lemma re_digamma_shiftedLine_le {d t : ℝ} (hdlt : 1 / 2 < d) (hd1 : d ≤ 1)
    (ht : 168 * π ≤ t) :
    (Complex.digamma (((1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I) / 2)).re
      ≤ Real.log t - Real.log 2 + 2 / 100 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  obtain ⟨hsre, hsim, -, -, -, -, -, hsnorm_pos, hsnorm_ub⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hs_ge_t : t ≤ ‖s‖ := le_norm_of_im_eq ht0 hsim
  have hz : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hsre]; linarith
  have hnorm_half : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  have hdig := re_digamma_le (C := 1) hz
    (by simpa using Complex.Stirling.norm_digammaRemainderIoi_le' (s / 2) hz 1 le_rfl)
  rw [show (1 / 2 + (1 : ℝ)) = 3 / 2 by norm_num] at hdig
  -- `log‖s/2‖ ≤ log t - log 2 + (1/2+d)/(168π)`
  have hlog_half : Real.log ‖s / 2‖ ≤ Real.log t + (1 / 2 + d) / (168 * π) - Real.log 2 := by
    rw [hnorm_half, Real.log_div hsnorm_pos.ne' (by norm_num)]
    have h3 := Real.log_add_le (u := 1 / 2 + d) (t := t) (by linarith) ht0
    have h4 : (1 / 2 + d) / t ≤ (1 / 2 + d) / (168 * π) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) ht
    linarith [Real.log_le_log hsnorm_pos hsnorm_ub]
  -- the digamma remainder fraction is `O(1/t)`
  have hfrac : (3 / 2 : ℝ) / ‖s / 2‖ ≤ 3 / (168 * π) := by
    rw [hnorm_half]
    calc (3 / 2 : ℝ) / (‖s‖ / 2) ≤ (3 / 2 : ℝ) / (t / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      _ = 3 / t := by ring
      _ ≤ 3 / (168 * π) := div_le_div_of_nonneg_left (by norm_num) (by positivity) ht
  have htiny : (1 / 2 + d) / (168 * π) + 3 / (168 * π) ≤ 2 / 100 := by
    rw [← add_div, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  linarith

/-- The Dirichlet term `Re(ζ'/ζ(s)) ≤ D` at a point `s` whose real part is a real abscissa
`σ > 1`, given the numerical von-Mangoldt bound `∑ₙ ‖Λ(n) n^{-σ}‖ ≤ D`. -/
private lemma re_logDeriv_riemannZeta_le_of_re {s : ℂ} {σ D : ℝ} (hσ : 1 < s.re) (hsre : s.re = σ)
    (hVM : ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ ≤ D) : (logDeriv riemannZeta s).re ≤ D := by
  refine (re_logDeriv_riemannZeta_le hσ).trans ?_
  rw [show (∑' n, ‖LSeries.term ↗Λ s n‖) = ∑' n, ‖LSeries.term ↗Λ (σ : ℂ) n‖ from
    tsum_congr fun n ↦ by rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsre, Complex.ofReal_re]]
  exact hVM

/-- Explicit log-`t` witness for the zero sum (`lem:le_zeta_sum_explicit`). For `d = 53/100`
(so `s_d = 103/100 + it`), `∑ᵢ Re 1/(s_d - ρᵢ) ≤ ½ log t + 39` for all `t ≥ 168π`: an explicit
constant for `tsum_re_inv_riemannXiZeros_sub_le`. -/
theorem tsum_re_inv_riemannXiZeros_sub_le_explicit (t : ℝ) (ht : 168 * π ≤ t) :
    ∑' i, (((1 / 2 : ℂ) + ((53 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + 39 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set d : ℝ := 53 / 100 with hd
  have hdlt : (1 / 2 : ℝ) < d := by rw [hd]; norm_num
  have hPair := summable_pairDensity (d := d) (t := t) hdlt
  obtain ⟨hsre, hsim, hre, hreσ, hs1, hsne, hsnorm_lb, -, -⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  have hs_ge1 : (1 : ℝ) ≤ ‖s‖ := le_trans (by rw [hd]; norm_num) hsnorm_lb
  -- (1) Dirichlet term `Re(ζ'/ζ) ≤ 35`
  have hsre103 : s.re = 103 / 100 := by rw [hsre, hd]; norm_num
  have hDir35 : (logDeriv riemannZeta s).re ≤ 35 :=
    re_logDeriv_riemannZeta_le_of_re hreσ hsre103 tsum_vonMangoldt_norm_le
  -- (2) polar terms `≤ 1`
  have b2 : (1 / s).re ≤ 1 := Complex.one_div_re_le_one hs_ge1
  have hs1im : (s - 1).im = t := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
  have b3 : (1 / (s - 1)).re ≤ 1 := Complex.one_div_re_le_one
    ((by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ t).trans (le_norm_of_im_eq ht0 hs1im))
  -- (3) digamma term with explicit remainder constant `C_R = 1`; here `-½ log 2 ≤ 0` is dropped
  have hpsi_bound : 1 / 2 * (Complex.digamma (s / 2)).re ≤ 1 / 2 * Real.log t + 3 / 2 := by
    have hcore := re_digamma_shiftedLine_le hdlt (by rw [hd]; norm_num) ht
    rw [← hsdef] at hcore
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  -- solve the explicit formula for the zero sum (`tsum_re_inv_riemannXiZeros_sub_eq`) and bound
  -- each of the five right-hand terms; `-½ log π ≤ 0` is dropped here.
  have hlogπ_nonneg : 0 ≤ 1 / 2 * Real.log π :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Real.pi_gt_three]))
  rw [tsum_re_inv_riemannXiZeros_sub_eq hre hs1 hsne hPair]
  linarith [b2, b3, hpsi_bound, hDir35, hlogπ_nonneg]

/-- Tight log-`t` witness for the zero sum at depth `d = 74/100`, parametric in the Dirichlet
input (`lem:ls_Cpsi`, `lem:ls_Cpsi_sharp`). At `s_d = 124/100 + it`,
`∑ᵢ Re 1/(s_d - ρᵢ) ≤ ½ log t + (D - 3/5)` for `t ≥ 168π`, given only the Dirichlet bound
`Re(ζ'/ζ(s_d)) ≤ D` supplied through `hVM`. -/
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_of {t D : ℝ} (ht : 168 * π ≤ t)
    (hVM : ∑' n, ‖LSeries.term ↗Λ ((124 / 100 : ℝ) : ℂ) n‖ ≤ D) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + (D - 3 / 5) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have ht500 : (500 : ℝ) ≤ t := le_trans (by nlinarith [Real.pi_gt_three]) ht
  set d : ℝ := 74 / 100 with hd
  have hdlt : (1 / 2 : ℝ) < d := by rw [hd]; norm_num
  have hPair := summable_pairDensity (d := d) (t := t) hdlt
  obtain ⟨hsre, hsim, hre, hreσ, hs1, hsne, -, -, -⟩ := shiftedLine_setup hdlt ht0
  set s : ℂ := (1 / 2 : ℂ) + (d : ℂ) + (t : ℂ) * I with hsdef
  -- (1) Dirichlet term `Re(ζ'/ζ(s_d)) ≤ D`, supplied through `hVM`
  have hDir : (logDeriv riemannZeta s).re ≤ D :=
    re_logDeriv_riemannZeta_le_of_re hreσ (by rw [hsre, hd]; norm_num) hVM
  -- (2) polar terms, tight `O(1/t)`: `‖s‖, ‖s - 1‖ ≥ t ≥ 500` from the imaginary part
  have hinv500 : t⁻¹ ≤ 1 / 500 := by rw [one_div]; exact inv_anti₀ (by norm_num) ht500
  have b2 : (1 / s).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv s).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hsim)).trans hinv500)
  have hs1im : (s - 1).im = t := by rw [Complex.sub_im, Complex.one_im, hsim]; ring
  have b3 : (1 / (s - 1)).re ≤ 1 / 500 := (Complex.re_one_div_le_norm_inv _).trans
    ((inv_anti₀ ht0 (le_norm_of_im_eq ht0 hs1im)).trans hinv500)
  -- (3) digamma term, keeping `-½ log 2` and an `O(1/t)` remainder
  have hpsi_bound : 1 / 2 * (Complex.digamma (s / 2)).re
      ≤ 1 / 2 * Real.log t + 1 / 100 - 1 / 2 * Real.log 2 := by
    have hcore := re_digamma_shiftedLine_le hdlt (by rw [hd]; norm_num) ht
    rw [← hsdef] at hcore
    linarith
  -- `-½ log π ≤ -½` since `log π ≥ 1` (as `π > 3 > e`)
  have hlogπ_ge : (1 : ℝ) ≤ Real.log π := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1)
      (le_of_lt (lt_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)) Real.pi_gt_three))
  have hlog2_ge := Real.log_two_gt_d9
  -- solve the explicit formula for the zero sum (`tsum_re_inv_riemannXiZeros_sub_eq`) and bound
  -- each of the five right-hand terms; here `-½ log π ≤ -½` and `-½ log 2` are both kept.
  rw [tsum_re_inv_riemannXiZeros_sub_eq hre hs1 hsne hPair]
  linarith [b2, b3, hpsi_bound, hDir, hlogπ_ge, hlog2_ge]

/-- Tight log-`t` witness for the zero sum (`lem:ls_Cpsi`): additive constant
`28/5 - 3/5 = 5`. -/
theorem tsum_re_inv_riemannXiZeros_sub_le_tight (t : ℝ) (ht : 168 * π ≤ t) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + 5 := by
  linarith [tsum_re_inv_riemannXiZeros_sub_le_tight_of ht tsum_vonMangoldt_norm_le_124]

/-- Sharp log-`t` witness for the zero sum (`lem:ls_Cpsi_sharp`): additive constant
`379/100 - 3/5 = 319/100`. -/
theorem tsum_re_inv_riemannXiZeros_sub_le_tight_sharp (t : ℝ) (ht : 168 * π ≤ t) :
    ∑' i, (((1 / 2 : ℂ) + ((74 / 100 : ℝ) : ℂ) + (t : ℂ) * I - riemannXiZeros i)⁻¹).re
      ≤ 1 / 2 * Real.log t + 319 / 100 := by
  linarith [tsum_re_inv_riemannXiZeros_sub_le_tight_of ht tsum_vonMangoldt_norm_le_124_sharp]

