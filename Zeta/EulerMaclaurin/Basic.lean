/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Summation.Complex
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Euler–Maclaurin expansion of the Riemann zeta function (region `Re s > 1`)

The Euler–Maclaurin expansion of `riemannZeta s` in the region of absolute convergence
`Re s > 1`, with the improper (`(N, ∞)`) remainder integral of the zeta summand
`f_s(x) = (x : ℂ)⁻ˢ`.

## Main definitions

- `Complex.eulerMaclaurinRemainderIoi`: the improper Euler–Maclaurin remainder.

## Main results

- `Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow`: absolute convergence of the
  zeta remainder integral for `Re s + p > 1`.
- `riemannZeta_eq_of_one_lt_re`: the Euler–Maclaurin expansion of `riemannZeta s` for `Re s > 1`.
-/
@[expose] public section


open MeasureTheory Filter Topology
open scoped Nat

namespace Complex

/-- For `c.re < 0`, the natural-indexed powers `(R : ℂ)^c` tend to `0` as `R → ∞`. -/
theorem tendsto_natCast_cpow_nhds_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun R : ℕ ↦ (R : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp
    tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [Function.comp_apply, neg_neg]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hR) c).symm

/-- **Integrability of the kernel times a complex power.** For `1 ≤ N` and `w.re < -1`, the
function `x ↦ B̃_p(x) · (x:ℂ)^w` is integrable on `(N, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_mul_cpow (p N : ℕ) (hN : 1 ≤ N) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact Complex.integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p (h := fun x : ℝ ↦ x ^ w.re)
    (integrableOn_Ioi_rpow_of_lt hw hN0)
    (Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N) w) fun x hx ↦
      le_of_eq (Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le) w)

/-- **The improper Euler–Maclaurin remainder**
`(-1)^(p+1)/p! · ∫_{(a,∞)} B̃_p(x) · f⁽ᵖ⁾(x) dx`, the `R → ∞` limit of the compact-interval
remainder `eulerMaclaurinRemainder p f a R`.

Unlike `eulerMaclaurinRemainder` this is an improper integral over `Set.Ioi a`; the two agree
only where that integral converges. -/
noncomputable def eulerMaclaurinRemainderIoi (p : ℕ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi a, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x

/-- **Absolute convergence of the zeta remainder integral.** For `1 ≤ N` and `Re s + p > 1`,
the integrand `B̃_p(x) · f_s⁽ᵖ⁾(x)` of the order-`p` Euler–Maclaurin remainder is integrable on
`(N, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow
    (s : ℂ) (p N : ℕ) (hN : 1 ≤ N) (hsp : 1 < s.re + p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (-s - (p : ℂ)).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith
  -- The closed form `f_s⁽ᵖ⁾(x) = (-1)^p (s)_p x^{-s-p}` reduces this to the
  -- kernel-times-power case.
  have h : IntegrableOn (fun x : ℝ ↦ (-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s *
      ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hw).const_mul _
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.iteratedDeriv_cpow_ofReal_neg s p (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le)]
  ring

end Complex

/-- **Euler–Maclaurin expansion of `riemannZeta s` for `Re s > 1`.** For `1 ≤ N` and order
`p = 2M+1`,
`ζ(s) = ∑_{n=1}^{N-1} n⁻ˢ + N^{1-s}/(s-1) + N⁻ˢ/2
          + ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · N^{-s-(2k-1)} + R_M(s, N)`,
with the improper remainder `R_M(s,N) = Complex.eulerMaclaurinRemainderIoi (2M+1) f_s N`. -/
theorem riemannZeta_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (M N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  have hsne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hsum : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    simpa only [one_div, ← Complex.cpow_neg] using
      (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  -- `∑' n, n⁻ˢ = ζ(s)`.
  have hzeta : ∑' (n : ℕ), (n : ℂ) ^ (-s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.tsum_eq_zero_add,
      Nat.cast_zero, Complex.zero_cpow hs0, zero_add]
    exact tsum_congr fun n ↦ by rw [one_div, ← Complex.cpow_neg]; push_cast; ring_nf
  -- Limit of the left-hand partial sums.
  have hLHS : Tendsto (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) atTop
      (𝓝 ((∑' (n : ℕ), (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s))) := by
    have htsum : Tendsto (fun R : ℕ ↦ ∑ i ∈ Finset.range (R + 1), (i : ℂ) ^ (-s)) atTop
        (𝓝 (∑' (n : ℕ), (n : ℂ) ^ (-s))) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply (htsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [show Finset.Icc N R = Finset.Ico N (R + 1) from by
          ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; lia,
      Finset.sum_Ico_eq_sub _ (by lia : N ≤ R + 1)]
  -- Limit of the remainder integral.
  have hsp : 1 < s.re + ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith
  have hint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun (2 * M + 1) (Int.fract x) : ℂ) *
      iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) :=
    Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s (2 * M + 1) N hN hsp
  have hrem : Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)) atTop
      (𝓝 (Complex.eulerMaclaurinRemainderIoi (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _ hint tendsto_natCast_atTop_atTop).const_mul _
  -- Limits of the vanishing `R`-power terms.
  have h1s : (1 - s).re < 0 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hns : (-s).re < 0 := by rw [Complex.neg_re]; linarith
  have hT1 : Tendsto (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)) atTop
      (𝓝 (((0 : ℂ) - (N : ℂ) ^ (1 - s)) / (1 - s))) :=
    ((Complex.tendsto_natCast_cpow_nhds_zero h1s).sub_const _).div_const _
  have hT2 : Tendsto (fun R : ℕ ↦ ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2) atTop
      (𝓝 (((N : ℂ) ^ (-s) + 0) / 2)) :=
    (Tendsto.const_add _ (Complex.tendsto_natCast_cpow_nhds_zero hns)).div_const _
  have hT3 : Tendsto (fun R : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))) atTop
      (𝓝 (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))) := by
    apply tendsto_finsetSum
    intro k _
    have hek : (-s - ((2 * k - 1 : ℕ) : ℂ)).re < 0 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) (2 * k - 1); linarith
    exact Tendsto.const_mul _ ((Complex.tendsto_natCast_cpow_nhds_zero hek).sub_const _)
  -- Assemble the limit of the right-hand side and identify it with that of the left side.
  have hRHS := (((hT1.add hT2).sub hT3).add hrem)
  have heq : (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
          + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
          - (∑ k ∈ Finset.Icc 1 M,
              ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                * (ascPochhammer ℂ (2 * k - 1)).eval s
                * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
          + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
              (N : ℝ) (R : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with R hR
    exact Complex.sum_cpow_eq s hsne1 M N R hN hR
  have hkey := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  -- Solve for `ζ(s)` and simplify the limit.
  rw [hzeta] at hkey
  have hconv : ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s) = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp [Complex.zero_cpow hs0]
  have hbern : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
            * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1' : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hsne1
  rw [hconv, hbern, sub_eq_iff_eq_add] at hkey
  rw [hkey]
  field_simp
  ring
