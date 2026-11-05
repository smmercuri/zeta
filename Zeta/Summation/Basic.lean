/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The Euler–Maclaurin summation formula

The Euler–Maclaurin summation formula for a function `f : ℝ → E` valued in a real Banach space
`E` (blueprint `euler_maclaurin.tex`). The Bernoulli kernel acts on the integrand as a *real*
scalar, so the real- and complex-valued formulas are one and the same theorem; the file
`Zeta/Summation/Complex.lean` carries only the `ℂ`-flavoured restatement.

## Main definitions

- `eulerMaclaurinRemainder`: the periodized-Bernoulli remainder `R_p(f; a, b)`.

## Main results

- `eulerMaclaurin_sum_eq`: the Euler–Maclaurin summation formula with that remainder.

The tower lemmas leading to `eulerMaclaurin_sum_eq` are `private`.
-/
@[expose] public section


open MeasureTheory

open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


/-- **Per-interval Euler–Maclaurin step.** The trapezoidal rule with remainder on the unit
interval `[n, n+1]`, for real `n`:
`∫ₙⁿ⁺¹ f = (f n + f (n+1))/2 - ∫ₙⁿ⁺¹ B₁(x - n) · f'(x) dx`. -/
private theorem integral_interval_eq {f f' : ℝ → E} {n : ℝ}
    (hf : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume n (n + 1)) :
    ∫ x in n..(n + 1), f x
      = (2⁻¹ : ℝ) • (f n + f (n + 1)) - ∫ x in n..(n + 1), bernoulliFun 1 (x - n) • f' x := by
  -- Integration by parts with `u = B₁(· - n)`, `u' = 1`, `v = f`, `v' = f'`.
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun 1 (y - n)) ((fun _ ↦ (1 : ℝ)) x) x := by
    intro x _
    have hcomp := (hasDerivAt_bernoulliFun 1 (x - n)).comp x ((hasDerivAt_id x).sub_const n)
    simp only [Nat.cast_one, Nat.sub_self, bernoulliFun_zero, mul_one] at hcomp
    exact hcomp
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hf intervalIntegrable_const hf'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_one, one_smul] at key
  simp only [bernoulliFun_one]
  rw [key]
  module

/-- **Unit-interval Euler–Maclaurin step**: the case `n = 0` of `integral_interval_eq`. -/
private theorem integral_unitInterval_eq {f f' : ℝ → E}
    (hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume 0 1) :
    ∫ x in (0 : ℝ)..1, f x
      = (2⁻¹ : ℝ) • (f 0 + f 1) - ∫ x in (0 : ℝ)..1, bernoulliFun 1 x • f' x := by
  have h := integral_interval_eq (n := 0) (f := f) (f' := f')
    (by simpa using hf) (by simpa using hf')
  simpa only [zero_add, sub_zero] using h

/-- **Order-raising recurrence for the Euler–Maclaurin tower.** The order-`q` remainder integral
over `[n, n+1]` in terms of the order-`(q+1)` one, for `q ≠ 0`. -/
private theorem integral_bernoulliFun_smul_eq {g g' : ℝ → E} {n : ℝ} {q : ℕ} (hq : q ≠ 0)
    (hg : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' volume n (n + 1)) :
    ∫ x in n..(n + 1), bernoulliFun q (x - n) • g x
      = ((bernoulli (q + 1) : ℝ) / ((q : ℝ) + 1)) • (g (n + 1) - g n)
        - (1 / ((q : ℝ) + 1)) • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  -- The antiderivative `u(x) = B_{q+1}(x - n)/(q+1)` has `u'(x) = B_q(x - n)`.
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun (q + 1) (y - n) / ((q : ℝ) + 1))
        (bernoulliFun q (x - n)) x := by
    intro x _
    have hcomp := ((hasDerivAt_bernoulliFun (q + 1) (x - n)).comp x
      ((hasDerivAt_id x).sub_const n)).div_const ((q : ℝ) + 1)
    have hval : ((q + 1 : ℕ) : ℝ) * bernoulliFun ((q + 1) - 1) (x - n) * 1 / ((q : ℝ) + 1)
        = bernoulliFun q (x - n) := by
      rw [show (q + 1) - 1 = q by lia, mul_one]; push_cast
      exact mul_div_cancel_left₀ _ hq1
    rwa [hval] at hcomp
  have hu' : IntervalIntegrable (fun x ↦ bernoulliFun q (x - n)) volume n (n + 1) :=
    (by fun_prop : Continuous fun x ↦ bernoulliFun q (x - n)).intervalIntegrable _ _
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hg hu' hg'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_eval_zero,
    bernoulliFun_endpoints_eq_of_ne_one (show q + 1 ≠ 1 by lia)] at key
  -- Factor the constant `1/(q+1)` out of the order-`(q+1)` integral.
  have hfac : (∫ x in n..(n + 1), (bernoulliFun (q + 1) (x - n) / ((q : ℝ) + 1)) • g' x)
      = ((q : ℝ) + 1)⁻¹ • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
    simp_rw [div_eq_inv_mul, mul_smul, intervalIntegral.integral_smul]
  rw [hfac] at key
  rw [one_div, smul_sub, key]
  module

/-- **Per-interval Euler–Maclaurin tower (raw form).** For a family `F 0, …, F p` on `[n, n+1]`
with `F (q+1)` the derivative of `F q`,
`∫ₙⁿ⁺¹ F 0 = (F 0 n + F 0 (n+1))/2 + ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · ΔF q`
`+ (-1)^p/p! · ∫ₙⁿ⁺¹ B_p(x-n)·F p`, with `ΔF q = F q (n+1) - F q n`.
This is the tower before the even/odd collapse of the Bernoulli sum. -/
private theorem integral_interval_eq_tower {n : ℝ} (F : ℕ → ℝ → E) {p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume n (n + 1)) :
    ∫ x in n..(n + 1), F 0 x
      = (2⁻¹ : ℝ) • (F 0 n + F 0 (n + 1))
        + ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (n + 1) - F q n)
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∫ x in n..(n + 1), bernoulliFun p (x - n) • F p x := by
  revert hderiv hF_int
  induction p, hp using Nat.le_induction with
  | base =>
    intro hderiv hF_int
    have hbase := integral_interval_eq (f := F 0) (f' := F 1)
      (hderiv 0 one_pos) (hF_int 1 one_pos le_rfl)
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    rw [hbase]
    module
  | succ p hp ih =>
    intro hderiv hF_int
    have IH := ih (fun q hq ↦ hderiv q (Nat.lt_succ_of_lt hq))
      (fun q hq0 hqp ↦ hF_int q hq0 (hqp.trans (Nat.le_succ p)))
    have hrec := integral_bernoulliFun_smul_eq (g := F p) (g' := F (p + 1)) (n := n) (q := p)
      (Nat.one_le_iff_ne_zero.mp hp) (hderiv p (Nat.lt_succ_self p))
      (hF_int (p + 1) (Nat.succ_pos p) le_rfl)
    rw [Finset.sum_Ico_succ_top (by lia : 1 ≤ p), IH, hrec, pow_succ, Nat.factorial_succ]
    have hp0 : (p ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    match_scalars <;> field_simp

/-- Each unit subinterval `[a+k, a+k+1]` (`k < N`) sits inside `[a, a+N]`. -/
private theorem uIcc_add_natCast_subset_uIcc (a : ℝ) {N k : ℕ} (hk : k < N) :
    Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) := by
  have hk1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  apply Set.uIcc_subset_uIcc <;> rw [Set.mem_uIcc] <;> left <;> constructor <;> linarith

/-- **Global Euler–Maclaurin tower (raw form).** The per-interval tower summed over the `N` unit
intervals `[a+n, a+n+1]`, with the Bernoulli boundary sum telescoped:
`∫ₐ^{a+N} F 0 = ∑_{n<N} (F 0 (a+n) + F 0 (a+n+1))/2
  + ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · (F q (a+N) - F q a)
  + (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`. -/
private theorem integral_eq_tower_sum {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∫ x in a..(a + N), F 0 x
      = (∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (F 0 (a + n) + F 0 (a + n + 1)))
        + (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  -- Each unit subinterval `[a+k, a+k+1]` sits inside `[a, a+N]`.
  have hsub : ∀ k, k < N → Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) :=
    fun _ hk ↦ uIcc_add_natCast_subset_uIcc a hk
  -- `F 0` is continuous on `[a, a+N]`, so its unit-interval integrals concatenate.
  have hcont0 : ContinuousOn (F 0) (Set.uIcc a (a + N)) := fun x hx ↦
    (hderiv 0 hp x hx).continuousAt.continuousWithinAt
  have hconcat :
      (∑ k ∈ Finset.range N, ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = ∫ x in a..(a + N), F 0 x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F 0)
      (a := fun k ↦ a + (k : ℝ)) (n := N)
      (fun k hk ↦ by
        have := (hcont0.mono (hsub k hk)).intervalIntegrable (μ := volume)
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using this)
    simpa [add_assoc] using h
  -- The per-interval tower applied on each `[a+k, a+k+1]`.
  have hstep : ∀ k ∈ Finset.range N,
      (∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = (2⁻¹ : ℝ) • (F 0 (a + (k : ℝ)) + F 0 (a + (k : ℝ) + 1))
          + (∑ q ∈ Finset.Ico 1 p,
              ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
                • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
          + ((-1 : ℝ) ^ p / (p ! : ℝ))
              • ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1),
                  bernoulliFun p (x - (a + (k : ℝ))) • F p x := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact integral_interval_eq_tower (n := a + (k : ℝ)) F hp
      (fun q hq x hx ↦ hderiv q hq x (hsub k hk hx))
      (fun q hq0 hqp ↦ (hF_int q hq0 hqp).mono_set (hsub k hk))
  -- Telescope the Bernoulli boundary differences.
  have hbern :
      (∑ k ∈ Finset.range N, ∑ q ∈ Finset.Ico 1 p,
          ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
            • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
        = ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ ↦ ?_)
    rw [← Finset.smul_sum]
    congr 1
    have h := Finset.sum_range_sub (fun k ↦ F q (a + (k : ℝ))) N
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
  -- Assemble: concatenate, expand each interval, distribute, telescope, factor.
  rw [← hconcat, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hbern, ← Finset.smul_sum, ← Finset.smul_sum]

omit [CompleteSpace E] in
/-- **Trapezoidal reindexing.** The trapezoidal sum over the `N` unit intervals starting at `a`
equals the full sum of the `N + 1` sample values minus half the two endpoint values. -/
private theorem sum_trapezoid_eq (a : ℝ) (g : ℝ → E) (N : ℕ) :
    ∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (g (a + (n : ℝ)) + g (a + (n : ℝ) + 1))
      = (∑ n ∈ Finset.range (N + 1), g (a + (n : ℝ))) - (2⁻¹ : ℝ) • (g a + g (a + (N : ℝ))) := by
  induction N with
  | zero => simp; module
  | succ M ih =>
    rw [Finset.sum_range_succ _ M, ih, Finset.sum_range_succ _ (M + 1)]
    push_cast
    simp only [← add_assoc]
    module

/-- **Euler–Maclaurin summation formula (raw form).** The value-sum counterpart of
`integral_eq_tower_sum`, for a family `F 0, …, F p` on `[a, a+N]`:
`∑_{n=0}^{N} F 0 (a+n) = ∫ₐ^{a+N} F 0 + (F 0 a + F 0 (a+N))/2
  - ∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · (F q (a+N) - F q a)
  - (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`. -/
private theorem sum_eq_tower_integral {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        - (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  rw [integral_eq_tower_sum F hp hderiv hF_int, sum_trapezoid_eq a (F 0) N]
  abel

omit [CompleteSpace E] in
/-- **Even/odd collapse of the Euler–Maclaurin Bernoulli sum.** For any coefficient family
`c : ℕ → E`,
`∑_{q=1}^{p-1} (-1)^q B_{q+1}/(q+1)! · c q = -∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · c (2k-1)`. -/
private theorem sum_Ico_bernoulli_collapse (c : ℕ → E) (p : ℕ) :
    ∑ q ∈ Finset.Ico 1 p,
        ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q
      = -∑ k ∈ Finset.Ico 1 (p / 2 + 1),
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)) • c (2 * k - 1) := by
  -- The terms with `q` even vanish, since then `q + 1` is odd and `≥ 3`.
  have hne : ∀ q ∈ Finset.Ico 1 p,
      ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q ≠ 0 → Odd q := by
    intro q hq hne0
    rw [Finset.mem_Ico] at hq
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    apply hne0
    simp [bernoulli_eq_zero_of_odd hodd.add_one (by lia)]
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_neg_distrib]
  -- Reindex the surviving odd `q = 2k - 1` by `k = (q + 1) / 2`.
  refine Finset.sum_bij' (fun q _ ↦ (q + 1) / 2) (fun k _ ↦ 2 * k - 1) ?_ ?_ ?_ ?_ ?_
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    obtain ⟨⟨_, hqp⟩, m, rfl⟩ := hq
    lia
  · rintro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨by lia, by lia⟩, k - 1, by lia⟩
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    change 2 * ((2 * m + 1 + 1) / 2) - 1 = 2 * m + 1
    lia
  · rintro k hk
    simp only [Finset.mem_Ico] at hk
    show (2 * k - 1 + 1) / 2 = k
    lia
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    -- `simp only [hi]` both beta-reduces `(fun k ↦ …) ((q + 1) / 2)` and rewrites the index.
    simp only [show (2 * m + 1 + 1) / 2 = m + 1 by lia]
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by lia, show 2 * (m + 1) = 2 * m + 1 + 1 by lia,
      Odd.neg_one_pow ⟨m, rfl⟩]
    module

/-- **Euler–Maclaurin summation formula (even-index form).** The value-sum tower with the
Bernoulli boundary sum folded onto the even indices:
`∑_{n=0}^{N} F 0 (a+n) = ∫ₐ^{a+N} F 0 + (F 0 a + F 0 (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (F (2k-1) (a+N) - F (2k-1) a)
  - (-1)^p/p! · ∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·F p`.
The remainder integrals are still the per-interval ones. -/
private theorem sum_eq_tower_integral_even {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (F (2 * k - 1) (a + N) - F (2 * k - 1) a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  have hcol := sum_Ico_bernoulli_collapse (fun q ↦ F q (a + N) - F q a) p
  -- Beta-reduce the `(fun q ↦ …) (2 * k - 1)` redexes left by instantiating `c`.
  beta_reduce at hcol
  rw [sum_eq_tower_integral F hp hderiv hF_int, hcol]
  abel

/-- **Per-interval Euler–Maclaurin tower (even-index form).** The classical
iterated-derivative form on a single unit interval `[n, n+1]`:
`∫ₙⁿ⁺¹ f = (f n + f (n+1))/2 - ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · Δf⁽²ᵏ⁻¹⁾`
`+ (-1)^p/p! · ∫ₙⁿ⁺¹ B_p(x-n)·f⁽ᵖ⁾`, with `Δg = g (n+1) - g n`. -/
private theorem integral_unitInterval_eq_tower {n : ℝ} {f : ℝ → E} {p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (iteratedDeriv q f) volume n (n + 1)) :
    ∫ x in n..(n + 1), f x
      = (2⁻¹ : ℝ) • (f n + f (n + 1))
        - (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (iteratedDeriv (2 * k - 1) f (n + 1) - iteratedDeriv (2 * k - 1) f n))
        + ((-1 : ℝ) ^ p / (p ! : ℝ))
            • ∫ x in n..(n + 1), bernoulliFun p (x - n) • iteratedDeriv p f x := by
  have hmain := integral_interval_eq_tower (n := n) (fun q ↦ iteratedDeriv q f) hp hderiv hf_int
  have hcol := sum_Ico_bernoulli_collapse
    (fun q ↦ iteratedDeriv q f (n + 1) - iteratedDeriv q f n) p
  beta_reduce at hcol
  simp only [iteratedDeriv_zero] at hmain ⊢
  rw [hmain, hcol]
  abel

omit [CompleteSpace E] in
/-- **Concatenation of the per-interval remainder integrals.** For an integer `a`,
`∑_{n<N} ∫_{a+n}^{a+n+1} B_p(x-(a+n))·G(x) dx = ∫_a^{a+N} B_p(Int.fract x)·G(x) dx`. -/
private theorem sum_integral_bernoulliFun_eq (a : ℤ) (p N : ℕ) (G : ℝ → E)
    (hG : IntervalIntegrable G volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range N,
        ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1), bernoulliFun p (x - ((a : ℝ) + n)) • G x
      = ∫ x in (a : ℝ)..((a : ℝ) + N), bernoulliFun p (Int.fract x) • G x := by
  -- On `(a+k, a+k+1]`, off the right endpoint, `Int.fract x = x - (a+k)`.
  have hker : ∀ k, k < N → ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.uIoc ((a : ℝ) + k) ((a : ℝ) + k + 1) →
        bernoulliFun p (x - ((a : ℝ) + k)) • G x = bernoulliFun p (Int.fract x) • G x := by
    intro k hk
    have hsing : {x : ℝ | x = (a : ℝ) + (k : ℝ) + 1}ᶜ ∈ (ae (volume : Measure ℝ)) := by
      rw [compl_mem_ae_iff, Set.ofPred_eq_eq_singleton]; exact Real.volume_singleton
    filter_upwards [hsing] with x hx hmem
    have hxne : x ≠ (a : ℝ) + (k : ℝ) + 1 := by simpa using hx
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    have hlt : x < (a : ℝ) + (k : ℝ) + 1 := lt_of_le_of_ne hmem.2 hxne
    have hfr : Int.fract x = x - ((a : ℝ) + (k : ℝ)) := by
      rw [← Int.fract_sub_intCast x (a + k), Int.fract_eq_self.mpr
        ⟨by push_cast; linarith [hmem.1], by push_cast; linarith⟩]
      push_cast; ring
    rw [hfr]
  -- Hence the periodized kernel is interval-integrable on each unit interval.
  have hint : ∀ k, k < N →
      IntervalIntegrable (fun x ↦ bernoulliFun p (Int.fract x) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) := by
    intro k hk
    have hHk : IntervalIntegrable (fun x ↦ bernoulliFun p (x - ((a : ℝ) + k)) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) :=
      (hG.mono_set (uIcc_add_natCast_subset_uIcc (a : ℝ) hk)).continuousOn_smul (by fun_prop)
    refine hHk.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hker k hk
  -- Replace each unit kernel, then concatenate via adjacent intervals.
  rw [Finset.sum_congr rfl (fun k hk ↦
    intervalIntegral.integral_congr_ae (hker k (Finset.mem_range.mp hk)))]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x ↦ bernoulliFun p (Int.fract x) • G x) (a := fun k ↦ (a : ℝ) + (k : ℝ)) (n := N)
    (fun k hk ↦ by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hint k hk)
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h


/-- **The Euler–Maclaurin remainder** `R_p(f; a, b) = (-1)^(p+1)/p! · ∫_a^b B̃_p(x) · f⁽ᵖ⁾(x) dx`,
with `B̃_p` the periodized Bernoulli function `bernoulliFun p (Int.fract x)` and
`f⁽ᵖ⁾ = iteratedDeriv p f`. The kernel is a *real* scalar, so this one definition serves any
real Banach space `E`. -/
noncomputable def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → E) (a b : ℝ) : E :=
  ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ))
    • ∫ x in a..b, bernoulliFun p (Int.fract x) • iteratedDeriv p f x

/-- **Euler–Maclaurin summation formula with remainder.** For an integer `a`, an order `p ≥ 1`
and `f : ℝ → E` whose iterated derivatives form a derivative chain on `[a, a+N]` and are
interval-integrable there,
`∑_{n=0}^{N} f(a+n) = ∫_a^{a+N} f + (f a + f (a+N))/2
  + ∑_{k=1}^{⌊p/2⌋} B_{2k}/(2k)! · (f⁽²ᵏ⁻¹⁾(a+N) - f⁽²ᵏ⁻¹⁾(a)) + R_p(f; a, a+N)`.
See `Complex.sum_eq` for the `ℂ`-flavoured restatement. -/
theorem eulerMaclaurin_sum_eq {f : ℝ → E} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (2⁻¹ : ℝ) • (f (a : ℝ) + f ((a : ℝ) + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  have hmain := sum_eq_tower_integral_even (a := (a : ℝ))
    (fun q ↦ iteratedDeriv q f) hp hderiv hf_int
  have hrem : eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N)
      = -(((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
          ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1),
            bernoulliFun p (x - ((a : ℝ) + n)) • iteratedDeriv p f x) := by
    rw [eulerMaclaurinRemainder, ← sum_integral_bernoulliFun_eq a p N
      (iteratedDeriv p f) (hf_int p hp le_rfl), pow_succ, ← neg_smul]
    congr 1
    ring
  simp only [iteratedDeriv_zero] at hmain ⊢
  rw [hmain, hrem]
  abel
