/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Summation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Complex-valued Euler–Maclaurin and the iterated derivatives of `x ↦ x⁻ˢ`

The `ℂ`-flavoured restatement of the Euler–Maclaurin formula of `Zeta/Summation/Basic.lean`,
together with the iterated derivatives of the zeta summand `f_s(x) = (x : ℂ)⁻ˢ`, which discharge
its derivative-chain hypothesis. Throughout, `(s)_j = (ascPochhammer ℂ j).eval s` is the rising
factorial.

## Main results

- `Complex.eulerMaclaurinRemainder_eq`: the generic Euler–Maclaurin remainder in
  `ℂ`-multiplicative form.
- `Complex.sum_eq`: the complex-valued Euler–Maclaurin summation formula.
- `Complex.iteratedDeriv_cpow_ofReal_neg`: the closed form of `(f_s)⁽ʲ⁾(x)` for `x > 0`.
- `Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg`: its `HasDerivAt` chain form.
- `Complex.sum_cpow_eq`: the finite Euler–Maclaurin expansion of `∑ n⁻ˢ`.
-/
@[expose] public section


open MeasureTheory
open scoped Topology Nat

namespace Complex

/-- **The Euler–Maclaurin remainder, in `ℂ`-multiplicative form**:
`R_p(f; a, b) = (-1)^(p+1)/p! · ∫_a^b B̃_p(x) · f⁽ᵖ⁾(x) dx`. -/
theorem eulerMaclaurinRemainder_eq (p : ℕ) (f : ℝ → ℂ) (a b : ℝ) :
    eulerMaclaurinRemainder p f a b
      = (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
        * ∫ x in a..b, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x := by
  rw [_root_.eulerMaclaurinRemainder]
  simp only [real_smul, ofReal_div, ofReal_pow, ofReal_neg, ofReal_one, ofReal_natCast]

/-- The periodized Bernoulli kernel `x ↦ B̃_p(x) = bernoulliFun p (Int.fract x)`, read as a
complex-valued function, is measurable. -/
theorem measurable_bernoulliFun_fract (p : ℕ) :
    Measurable (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ)) := by fun_prop

/-- **Uniform bound on the periodized Bernoulli kernel**: `B̃_p` is bounded by some `C ≥ 0`. -/
theorem exists_norm_bernoulliFun_fract_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖(bernoulliFun p (Int.fract x) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_bernoulliFun p).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rw [Complex.norm_real]
  exact (hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩).trans (le_max_left _ _)

/-- The complex power `x ↦ (x : ℂ) ^ w` is a.e.-strongly-measurable on `(c, ∞)` for any
`0 ≤ c`. -/
theorem aestronglyMeasurable_ofReal_cpow_Ioi {c : ℝ} (hc : 0 ≤ c) (w : ℂ) :
    AEStronglyMeasurable (fun x : ℝ ↦ (x : ℂ) ^ w) (volume.restrict (Set.Ioi c)) := by
  refine ContinuousOn.aestronglyMeasurable (fun x hx ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const x w
    (Or.inr (lt_of_le_of_lt hc (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt

/-- **Improper (`Ioi`) domination for periodized-Bernoulli-weighted integrands.** If a kernel
`K : ℝ → ℂ` is a.e.-strongly-measurable on `(c, ∞)` and dominated there by an integrable
majorant `h`, then `x ↦ B̃_p(x) · K(x)` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le (p : ℕ) {c : ℝ} {K : ℝ → ℂ}
    {h : ℝ → ℝ} (hh : IntegrableOn h (Set.Ioi c))
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Ioi c)))
    (hbound : ∀ x ∈ Set.Ioi c, ‖K x‖ ≤ h x) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * K x) (Set.Ioi c) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_bernoulliFun_fract_le p
  refine Integrable.mono' (g := fun x ↦ C * h x) (hh.const_mul C)
    ((measurable_bernoulliFun_fract p).aestronglyMeasurable.mul hK) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul]
  exact mul_le_mul (hC x) (hbound x hx) (norm_nonneg _) hC0

/-- **Complex-valued Euler–Maclaurin summation formula**, the `ℂ`-flavoured restatement of
`eulerMaclaurin_sum_eq`:
`∑_{n=0}^{N} f(a+n) = ∫_a^{a+N} f + (f a + f (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (f⁽²ᵏ⁻¹⁾(a+N) - f⁽²ᵏ⁻¹⁾(a)) + R_p(f; a, a+N)`. -/
theorem sum_eq {f : ℝ → ℂ} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (f (a : ℝ) + f ((a : ℝ) + N)) / 2
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  rw [eulerMaclaurin_sum_eq a hp hderiv hf_int]
  simp only [real_smul, ofReal_div, ofReal_inv, ofReal_natCast, ofReal_ofNat]
  ring

/-- The closed form `(-1)ʲ · (s)_j · (x : ℂ)^(-s - j)` of the `j`-th derivative of `x ↦ x⁻ˢ` has
as its own derivative the `(j+1)`-st member of the same family. -/
private theorem hasDerivAt_cpow_closed_form (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)))
      ((-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s * (x : ℂ) ^ (-s - ((j : ℂ) + 1)))
      x := by
  by_cases he : -s - (j : ℂ) = 0
  · -- `s = -j`: the power is the constant `1` and the new rising factorial vanishes.
    have hsj : s + (j : ℂ) = 0 := by linear_combination -he
    have hp : (ascPochhammer ℂ (j + 1)).eval s = 0 := by
      rw [ascPochhammer_succ_eval, hsj, mul_zero]
    rw [he, hp]
    simp only [Complex.cpow_zero, mul_one, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  · -- general case: differentiate the power via the cpow rule.
    have hpow := hasDerivAt_ofReal_cpow_const (r := -s - (j : ℂ)) hx.ne' he
    have key : (-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s
          * (x : ℂ) ^ (-s - ((j : ℂ) + 1))
        = ((-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s)
          * ((-s - (j : ℂ)) * (x : ℂ) ^ ((-s - (j : ℂ)) - 1)) := by
      rw [show -s - ((j : ℂ) + 1) = (-s - (j : ℂ)) - 1 from by ring, ascPochhammer_succ_eval]
      ring
    rw [key]
    exact hpow.const_mul _

/-- **Iterated derivatives of `x ↦ x⁻ˢ`.** For `x > 0`,
`(f_s)⁽ʲ⁾(x) = (-1)ʲ · (s)_j · (x : ℂ)^(-s - j)`. -/
theorem iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x
      = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) := by
  induction j generalizing x with
  | zero => simp [ascPochhammer_zero]
  | succ j ih =>
    have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
        =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ ih (Set.mem_Ioi.mp hy)
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_cpow_closed_form s j hx).deriv]
    push_cast
    ring

/-- **Derivative chain for `x ↦ x⁻ˢ`.** For `x > 0`, the `j`-th iterated derivative of
`f_s(x) = (x : ℂ)⁻ˢ` is differentiable with derivative the `(j+1)`-st iterated derivative
(the derivative-chain hypothesis of `Complex.sum_eq`). -/
theorem hasDerivAt_iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)))
      (iteratedDeriv (j + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) x := by
  have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
      =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx)
      fun y hy ↦ iteratedDeriv_cpow_ofReal_neg s j (Set.mem_Ioi.mp hy)
  rw [iteratedDeriv_cpow_ofReal_neg s (j + 1) hx]
  have hd := (hasDerivAt_cpow_closed_form s j hx).congr_of_eventuallyEq heq
  rw [show -s - ((j + 1 : ℕ) : ℂ) = -s - ((j : ℂ) + 1) by push_cast; ring]
  exact hd

/-- **Finite Euler–Maclaurin expansion of `∑ n⁻ˢ`.** For `s ≠ 1` and integers `1 ≤ N ≤ R`, at
order `p = 2M+1` and with `f_s(x) = (x : ℂ)⁻ˢ`,
`∑_{n=N}^{R} n⁻ˢ = (R^{1-s} - N^{1-s})/(1-s) + (N⁻ˢ + R⁻ˢ)/2
  - ∑_{k=1}^{M} B_{2k}/(2k)! · (s)_{2k-1} · (R^{-s-(2k-1)} - N^{-s-(2k-1)}) + R_{2M+1}(f_s; N, R)`.
-/
theorem sum_cpow_eq (s : ℂ) (hs : s ≠ 1) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
        + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
        - (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                  - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
        + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := Int.cast_natCast N
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hNR)
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have key := sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by positivity)
    (fun q _ x hx ↦ hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx))
    (fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx)).continuousAt.continuousWithinAt)
  -- Normalize the integer/natural casts and the boundary index set in `key`.
  rw [hRN, hNa, show Finset.Ico 1 ((2 * M + 1) / 2 + 1) = Finset.Icc 1 M from by
    ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; lia] at key
  -- Closed form for the iterated derivatives of `f` on `(0, ∞)`.
  have hDeriv_eq : ∀ (j : ℕ) (x : ℝ), 0 < x →
      iteratedDeriv j f x
        = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) :=
    fun j _ hx ↦ iteratedDeriv_cpow_ofReal_neg s j hx
  -- Rewrite the left-hand `Icc` sum as the `range` sum of `key`.
  have hLHS : ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range (R - N + 1), f ((N : ℝ) + (n : ℝ)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show R + 1 - N = R - N + 1 from by lia]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hf]; push_cast; ring_nf
  -- The integral via `integral_cpow`.
  have hIeq : (∫ x in (N : ℝ)..(R : ℝ), f x)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) := by
    simp only [hf]
    rw [integral_cpow (Or.inr ⟨fun h ↦ hs (neg_injective h), ?_⟩)]
    · rw [show -s + 1 = 1 - s from by ring]; push_cast; ring_nf
    · rw [Set.uIcc_of_le (by exact_mod_cast hNR : (N : ℝ) ≤ R), Set.mem_Icc]
      exact fun ⟨h1, _⟩ ↦ absurd h1 (not_le.mpr hN0)
  -- The endpoint correction (just a cast).
  have hEeq : (f (N : ℝ) + f (R : ℝ)) / 2 = ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2 := by
    simp only [hf]; push_cast; ring_nf
  -- Each Bernoulli boundary term collapses to the closed form, with a sign flip.
  have hBeq : ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)
          * (iteratedDeriv (2 * k - 1) f (R : ℝ) - iteratedDeriv (2 * k - 1) f (N : ℝ))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s
            * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hodd : (-1 : ℂ) ^ (2 * k - 1) = -1 :=
      Odd.neg_one_pow ⟨k - 1, by have := (Finset.mem_Icc.mp hk).1; lia⟩
    rw [hDeriv_eq _ _ hRpos, hDeriv_eq _ _ hN0, hodd]
    push_cast
    ring
  rw [hLHS, key, hIeq, hEeq, hBeq]
  ring

end Complex
