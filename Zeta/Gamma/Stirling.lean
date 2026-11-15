/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Zeta.Gamma.HalfPlane
public import Zeta.Summation.Complex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Euler–Maclaurin / Stirling expansion of the complex digamma function

The project's complex Euler–Maclaurin summation formula `Complex.sum_eq` specialised to the
kernel `g_s(x) = (s + x)⁻¹`, giving the finite Euler–Maclaurin expansion of the digamma partial
sum and the improper remainder together with its explicit bound.

## Main results

- `Complex.Stirling.iteratedDeriv_inv_add_ofReal`: `g_s⁽ʲ⁾(x) = (-1)ʲ · j! · (s + x)^(-(j+1))`.
- `Complex.Stirling.intervalIntegrable_iteratedDeriv_inv_add_ofReal`: interval integrability of
  each iterated derivative on intervals in `[0, ∞)`.
- `Complex.Stirling.sum_inv_add_eq_digamma_sub`: the digamma telescope
  `∑_{n=0}^{N} (s + n)⁻¹ = ψ(s + N + 1) - ψ(s)`.
- `Complex.Stirling.sum_inv_add_eq`: the finite Euler–Maclaurin expansion of the digamma partial
  sum.
- `Complex.Stirling.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add`: integrability of
  the improper Euler–Maclaurin remainder integrand on `(0, ∞)`.
- `Complex.Stirling.digammaRemainderIoi`: the improper (`(0, ∞)`) Euler–Maclaurin remainder of the
  digamma kernel.
- `Complex.Stirling.abs_bernoulliFun_le`: `|B_k(x)| ≤ 4 · k!/(2π)^k` on `[0, 1]`, for `k ≥ 1`.
- `Complex.Stirling.norm_digammaRemainderIoi_le'`: the explicit remainder bound
  `‖R_p(g_s; 0, ∞)‖ ≤ p!/(2π)^(p-1) · ‖s‖^(-p)`, uniformly for `Re s > 0`.
-/
@[expose] public section


open MeasureTheory
open scoped Topology Nat Real

namespace Complex.Stirling

/-- The set where the kernel `x ↦ (s + x)⁻¹` is defined is open. -/
private theorem isOpen_setOf_add_ofReal_ne_zero (s : ℂ) :
    IsOpen {y : ℝ | s + (y : ℂ) ≠ 0} :=
  isOpen_ne.preimage (continuous_const.add Complex.continuous_ofReal)

/-- For `Re s > 0` and `0 ≤ x`, the kernel denominator `s + x` is nonzero. -/
private theorem add_ofReal_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    s + (x : ℂ) ≠ 0 :=
  Complex.ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)

/-- The closed form `(-1)ʲ · j! · (s + x)^(-(j+1))` of the `j`-th derivative of the kernel
`x ↦ (s + x)⁻¹` differentiates to the `(j+1)`-st instance of the same family. The hypothesis is
`s + x ≠ 0`, since the power is an integer power. -/
private theorem hasDerivAt_inv_add_closed_form (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)))
      ((-1 : ℂ) ^ (j + 1) * ((j + 1)! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 + 1 : ℤ))) x := by
  have ha : HasDerivAt (fun w : ℂ ↦ s + w) 1 (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_add s
  have hres := (((hasDerivAt_zpow (-(j + 1 : ℤ)) (s + (x : ℂ)) (Or.inl hx)).comp (x : ℂ)
    ha).comp_ofReal).const_mul ((-1 : ℂ) ^ j * (j ! : ℂ))
  rw [show (-1 : ℂ) ^ (j + 1) * ((j + 1)! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 + 1 : ℤ))
      = (-1 : ℂ) ^ j * (j ! : ℂ)
        * (((-(j + 1) : ℤ) : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 : ℤ) - 1) * 1) from by
    rw [show (-(j + 1 + 1 : ℤ)) = (-(j + 1 : ℤ) - 1) from by ring]
    push_cast [Nat.factorial_succ]
    ring]
  exact hres

/-- Iterated derivatives of the kernel `x ↦ (s + x)⁻¹`: for `s + x ≠ 0`,
`g_s⁽ʲ⁾(x) = (-1)ʲ · j! · (s + x)^(-(j+1))`. -/
theorem iteratedDeriv_inv_add_ofReal (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x
      = (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 : ℤ)) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have heq : iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)
        =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)) :=
      Filter.eventually_of_mem ((isOpen_setOf_add_ofReal_ne_zero s).mem_nhds hx)
        fun y hy ↦ ih hy
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_inv_add_closed_form s j hx).deriv]
    push_cast
    ring

/-- Derivative chain for the kernel `x ↦ (s + x)⁻¹`: for `s + x ≠ 0`, the `j`-th iterated
derivative of `g_s` is differentiable with derivative the `(j+1)`-st iterated derivative. -/
theorem hasDerivAt_iteratedDeriv_inv_add_ofReal (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    HasDerivAt (iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹))
      (iteratedDeriv (j + 1) (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x) x := by
  have heq : iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)
      =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)) :=
    Filter.eventually_of_mem ((isOpen_setOf_add_ofReal_ne_zero s).mem_nhds hx)
      fun y hy ↦ iteratedDeriv_inv_add_ofReal s j hy
  rw [iteratedDeriv_inv_add_ofReal s (j + 1) hx]
  exact (hasDerivAt_inv_add_closed_form s j hx).congr_of_eventuallyEq heq

/-- Interval integrability of the kernel derivatives: for `Re s > 0`, every `j`, and all reals
`0 ≤ a`, `0 ≤ b`, the iterated derivative `g_s⁽ʲ⁾` is interval integrable on `[a, b]`. -/
theorem intervalIntegrable_iteratedDeriv_inv_add_ofReal (s : ℂ) (hs : 0 < s.re) (j : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx ↦ (hasDerivAt_iteratedDeriv_inv_add_ofReal s j
    (add_ofReal_ne_zero_of_re_pos hs ((le_min ha hb).trans hx.1))).continuousAt.continuousWithinAt

/-- Digamma telescope: for `Re s > 0` and `N : ℕ`,
`∑_{n=0}^{N} (s + n)⁻¹ = ψ(s + N + 1) - ψ(s)`, where `ψ = Complex.digamma`. -/
theorem sum_inv_add_eq_digamma_sub (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (s + (n : ℂ))⁻¹
      = Complex.digamma (s + (N : ℂ) + 1) - Complex.digamma s := by
  induction N with
  | zero =>
    rw [Finset.range_one, Finset.sum_singleton]
    simp only [Nat.cast_zero, add_zero]
    rw [Complex.digamma_apply_add_one s (ne_neg_natCast_of_re_pos hs)]
    ring
  | succ N ih =>
    have hre : 0 < (s + (N : ℂ) + 1).re := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [show s + ((N : ℂ) + 1) + 1 = s + (N : ℂ) + 1 + 1 from by ring,
      show s + ((N : ℂ) + 1) = s + (N : ℂ) + 1 from by ring,
      Complex.digamma_apply_add_one (s + (N : ℂ) + 1) (ne_neg_natCast_of_re_pos hre)]
    ring

/-- Finite Euler–Maclaurin expansion of the digamma partial sum: for `Re s > 0` and `M N : ℕ`,
with the kernel `g_s(x) = (s + x)⁻¹` and order `p = 2M+1`,
`ψ(s + N + 1) - ψ(s) = [Log(s + N) - Log s] + (1/s + 1/(s + N))/2
  - ∑_{k=1}^{M} B_{2k}/(2k) · ((s + N)^{-2k} - s^{-2k}) + R_{2M+1}(g_s; 0, N)`,
where `R_{2M+1}` is the complex Euler–Maclaurin remainder `eulerMaclaurinRemainder`. -/
theorem sum_inv_add_eq (s : ℂ) (hs : 0 < s.re) (M N : ℕ) :
    Complex.digamma (s + (N : ℂ) + 1) - Complex.digamma s
      = (Complex.log (s + (N : ℂ)) - Complex.log s)
        + (s⁻¹ + (s + (N : ℂ))⁻¹) / 2
        - (∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * k)
              * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ))))
        + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (s + (y : ℂ))⁻¹ with hf
  have hsub : Set.uIcc ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) ⊆ {y : ℝ | s + (y : ℂ) ≠ 0} := by
    rw [Int.cast_zero, zero_add, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    exact fun y hy ↦ add_ofReal_ne_zero_of_re_pos hs hy.1
  have hderiv : ∀ q, q < 2 * M + 1 → ∀ x ∈ {y : ℝ | s + (y : ℂ) ≠ 0},
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ hasDerivAt_iteratedDeriv_inv_add_ofReal s q hx
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 1 →
      IntervalIntegrable (iteratedDeriv q f) volume ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) := by
    intro q _ _
    rw [Int.cast_zero, zero_add]
    exact intervalIntegrable_iteratedDeriv_inv_add_ofReal s hs q le_rfl (by positivity)
  have key := Complex.sum_eq (f := f) (0 : ℤ) (N := N) (p := 2 * M + 1)
    (by positivity) (fun q hq x hx ↦ hderiv q hq x (hsub hx)) hint
  simp only [Int.cast_zero, zero_add] at key
  have hIco : Finset.Ico 1 ((2 * M + 1) / 2 + 1) = Finset.Icc 1 M := by
    ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; lia
  rw [hIco] at key
  -- Identify the left-hand sum of `key` with the digamma telescope.
  have hLHS : ∑ n ∈ Finset.range (N + 1), (s + (n : ℂ))⁻¹
      = ∑ n ∈ Finset.range (N + 1), f ((n : ℝ)) :=
    Finset.sum_congr rfl fun n _ ↦ by rw [hf]; push_cast; ring
  -- The integral term, by the fundamental theorem of calculus with antiderivative `Log (s + ·)`.
  have hIeq : (∫ x in (0 : ℝ)..(N : ℝ), f x) = Complex.log (s + (N : ℂ)) - Complex.log s := by
    rw [hf]
    have hderiv_log : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
        HasDerivAt (fun y : ℝ ↦ Complex.log (s + (y : ℂ))) ((s + (x : ℂ))⁻¹) x := by
      intro x hx
      have hx0 : 0 ≤ x := (le_min le_rfl (Nat.cast_nonneg N)).trans hx.1
      have hmem : s + (x : ℂ) ∈ Complex.slitPlane :=
        Or.inl (by rw [Complex.add_re, Complex.ofReal_re]; linarith)
      have haff : HasDerivAt (fun w : ℂ ↦ s + w) 1 (x : ℂ) := by
        simpa using (hasDerivAt_id (x : ℂ)).const_add s
      simpa using ((Complex.hasDerivAt_log hmem).comp (x : ℂ) haff).comp_ofReal
    have hintf : IntervalIntegrable f volume (0 : ℝ) (N : ℝ) := by
      simpa using intervalIntegrable_iteratedDeriv_inv_add_ofReal s hs 0 le_rfl
        (by positivity : (0 : ℝ) ≤ (N : ℝ))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_log hintf]
    simp
  -- The endpoint correction.
  have hEeq : (f 0 + f (N : ℝ)) / 2 = (s⁻¹ + (s + (N : ℂ))⁻¹) / 2 := by
    simp [hf]
  -- Each Bernoulli boundary term collapses to the closed form, with a sign flip.
  have hBeq : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * k - 1) f (N : ℝ) - iteratedDeriv (2 * k - 1) f 0))
      = -(∑ k ∈ Finset.Icc 1 M,
          (bernoulli (2 * k) : ℂ) / (2 * k)
            * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ)))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hfac : ((2 * k)! : ℂ) = (2 * k : ℂ) * ((2 * k - 1)! : ℂ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by lia : 2 * k ≠ 0)).symm
    have h2k : (2 * k : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by lia))
    have hfne : ((2 * k - 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hf,
      iteratedDeriv_inv_add_ofReal s (2 * k - 1) (add_ofReal_ne_zero_of_re_pos hs (by positivity)),
      iteratedDeriv_inv_add_ofReal s (2 * k - 1) (add_ofReal_ne_zero_of_re_pos hs le_rfl),
      show (-1 : ℂ) ^ (2 * k - 1) = -1 from by
        rw [show 2 * k - 1 = 2 * (k - 1) + 1 from by lia, pow_succ, pow_mul]; simp,
      show (-(((2 * k - 1 : ℕ) : ℤ) + 1)) = -(2 * k : ℤ) from by lia]
    push_cast
    rw [hfac]
    simp only [add_zero]
    field_simp
    ring
  rw [← sum_inv_add_eq_digamma_sub s hs N, hLHS, key, hIeq, hEeq, hBeq]
  ring

/-- Antitonicity of the negative integer power `t ↦ t^(-(p+1))` on the positive reals: for
`0 < a ≤ b`, `b^(-(p+1)) ≤ a^(-(p+1))`. -/
private theorem zpow_neg_add_one_le_of_le {p : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(↑p + 1 : ℤ)) ≤ a ^ (-(↑p + 1 : ℤ)) := by
  rw [show (-(↑p + 1 : ℤ)) = -↑(p + 1) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
    zpow_natCast]
  simpa using one_div_le_one_div_of_le (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)

/-- Integrability of the pure power kernel `‖s + x‖^(-(p+1))` on `(0, ∞)`, for `Re s > 0` and
`p ≥ 1`. -/
private theorem integrableOn_Ioi_norm_zpow_inv_add (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))) (Set.Ioi (0 : ℝ)) := by
  -- `Re s + x ≤ ‖s + x‖`, whence both `Re s ≤ ‖s + x‖` (used near `0`) and `x ≤ ‖s + x‖` (tail).
  have hsum : ∀ x : ℝ, s.re + x ≤ ‖s + (x : ℂ)‖ := fun x ↦ by
    simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm (s + (x : ℂ))
  have hmeas : Measurable (fun x : ℝ ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))) := by fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  apply IntegrableOn.union
  · apply Integrable.mono' (g := fun _ : ℝ ↦ s.re ^ (-(↑p + 1 : ℤ)))
      continuous_const.integrableOn_Ioc hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact zpow_neg_add_one_le_of_le hs (by linarith [hsum x, hx.1.le])
  · have hg2int : IntegrableOn (fun x : ℝ ↦ x ^ (-(↑p + 1 : ℤ))) (Set.Ioi (1 : ℝ)) := by
      have hlt : (-(↑p + 1 : ℝ)) < -1 := by
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
        linarith
      apply (integrableOn_Ioi_rpow_of_lt hlt one_pos).congr_fun _ measurableSet_Ioi
      intro x _
      change x ^ (-(↑p + 1 : ℝ)) = x ^ (-(↑p + 1 : ℤ))
      rw [← Real.rpow_intCast x (-(↑p + 1 : ℤ))]; congr 1; push_cast; ring
    apply Integrable.mono' (g := fun x : ℝ ↦ x ^ (-(↑p + 1 : ℤ))) hg2int
      hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      rw [Real.norm_of_nonneg (by positivity)]
      exact zpow_neg_add_one_le_of_le hx0 (by linarith [hsum x, hs.le])

/-- The integral `∫₀^∞ ‖s + x‖^(-(p+1)) dx ≤ κ · ‖s‖^(-p)`, the sharp `‖s‖`-decay, for
`Re s > 0` and `p ≥ 1`, with `κ = ∫₀^∞ (1 + w²)⁻¹ dw`. -/
private theorem integral_Ioi_norm_zpow_inv_add_le (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    ∫ x in Set.Ioi (0 : ℝ), ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))
      ≤ (∫ w in Set.Ioi (0 : ℝ), (1 + w ^ 2)⁻¹) * ‖s‖ ^ (-(p : ℤ)) := by
  set r := ‖s‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs)
  set F : ℝ → ℝ := fun x ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))
  have hscale : ∫ x in Set.Ioi (0 : ℝ), F x = r * ∫ x in Set.Ioi (0 : ℝ), F (r * x) := by
    have := MeasureTheory.integral_comp_mul_left_Ioi F 0 hr0
    simp only [mul_zero, smul_eq_mul] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
  have hdomint : IntegrableOn (fun x : ℝ ↦ r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹)
      (Set.Ioi (0 : ℝ)) := (integrable_inv_one_add_sq.const_mul _).integrableOn
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ), F (r * x) ≤ r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹ := by
    intro x hx
    have hx0 : 0 < x := hx
    have hA0 : 0 < ‖s + ((r * x : ℝ) : ℂ)‖ :=
      norm_pos_iff.mpr (add_ofReal_ne_zero_of_re_pos hs (by positivity))
    have hkey : r ^ (p + 1) * (1 + x ^ 2) ≤ ‖s + ((r * x : ℝ) : ℂ)‖ ^ (p + 1) := by
      set A := ‖s + ((r * x : ℝ) : ℂ)‖ with hA
      have hrsq : r ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hAsq : A ^ 2 = (s.re + r * x) ^ 2 + s.im ^ 2 := by
        rw [hA, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
        ring
      have hsq : r ^ 2 * (1 + x ^ 2) ≤ A ^ 2 := by
        rw [hAsq, hrsq]
        nlinarith [mul_nonneg hs.le (mul_nonneg hr0.le hx0.le)]
      have hAr : r ≤ A :=
        le_of_sq_le_sq (le_trans (by nlinarith [sq_nonneg x, hr0.le]) hsq) hA0.le
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by lia⟩
      calc r ^ (m + 1 + 1) * (1 + x ^ 2)
          = r ^ m * (r ^ 2 * (1 + x ^ 2)) := by ring
        _ ≤ A ^ m * A ^ 2 := mul_le_mul (pow_le_pow_left₀ hr0.le hAr m) hsq (by positivity)
              (pow_nonneg hA0.le m)
        _ = A ^ (m + 1 + 1) := by ring
    change ‖s + ((r * x : ℝ) : ℂ)‖ ^ (-(↑p + 1 : ℤ)) ≤ _
    rw [show (-(↑p + 1 : ℤ)) = -↑(p + 1) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, ← mul_inv]
    simpa using one_div_le_one_div_of_le (by positivity) hkey
  have hFrint : IntegrableOn (fun x : ℝ ↦ F (r * x)) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff F 0 hr0).mpr
      (by rw [mul_zero]; exact integrableOn_Ioi_norm_zpow_inv_add s hs p hp)
  rw [hscale]
  have hpow : r * r ^ (-(↑p + 1 : ℤ)) = r ^ (-(p : ℤ)) := by
    have h1 : (-(p : ℤ)) = 1 + (-(↑p + 1)) := by ring
    rw [h1, zpow_add₀ hr0.ne', zpow_one]
  calc r * ∫ x in Set.Ioi (0 : ℝ), F (r * x)
      ≤ r * ∫ x in Set.Ioi (0 : ℝ), r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hFrint hdomint measurableSet_Ioi hpt) hr0.le
    _ = (r * r ^ (-(↑p + 1 : ℤ))) * ∫ x in Set.Ioi (0 : ℝ), (1 + x ^ 2)⁻¹ := by
        rw [integral_const_mul]; ring
    _ = (∫ w in Set.Ioi (0 : ℝ), (1 + w ^ 2)⁻¹) * ‖s‖ ^ (-(p : ℤ)) := by rw [hpow, ← hr]; ring

/-- Absolute convergence of the digamma remainder integral: for `Re s > 0` and `p ≥ 1`, the
integrand `B̃_p(x) · g_s⁽ᵖ⁾(x)` of the order-`p` Euler–Maclaurin remainder is integrable on
`(0, ∞)`. -/
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add
    (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x) (Set.Ioi (0 : ℝ)) := by
  have hCF : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
      ((-1 : ℂ) ^ p * (p ! : ℂ) * (s + (x : ℂ)) ^ (-(↑p + 1 : ℤ)))) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p
      (h := fun x : ℝ ↦ (p ! : ℝ) * ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)))
      ((integrableOn_Ioi_norm_zpow_inv_add s hs p hp).const_mul _)
      (by fun_prop : Measurable (fun x : ℝ ↦
        (-1 : ℂ) ^ p * (p ! : ℂ) * (s + (x : ℂ)) ^ (-(↑p + 1 : ℤ)))).aestronglyMeasurable
      (fun x _ ↦ le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
  apply hCF.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  dsimp only
  rw [iteratedDeriv_inv_add_ofReal s p (add_ofReal_ne_zero_of_re_pos hs hx0.le)]

/-- The improper digamma Euler–Maclaurin remainder
`R_p(g_s; 0, ∞) = (-1)^(p+1)/p! · ∫_{(0,∞)} B̃_p(x) · g_s⁽ᵖ⁾(x) dx`, the improper (`(0, ∞)`)
analogue of `eulerMaclaurinRemainder` for the digamma kernel `g_s(x) = (s + x)⁻¹`. -/
noncomputable def digammaRemainderIoi (s : ℂ) (p : ℕ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x

/-- Shared norm bound for the digamma remainder: for `Re s > 0`, `p ≥ 1`, and `CB` a bound on
the periodized Bernoulli kernel norm, `‖R_p(g_s; 0, ∞)‖ ≤ CB · (π/2) · ‖s‖^(-p)`. -/
private theorem norm_digammaRemainderIoi_le_of_bound {s : ℂ} (hs : 0 < s.re)
    {p : ℕ} (hp : 1 ≤ p) {CB : ℝ} (hCB : ∀ x : ℝ, ‖(bernoulliFun p (Int.fract x) : ℂ)‖ ≤ CB) :
    ‖digammaRemainderIoi s p‖ ≤ CB * (π / 2) * ‖s‖ ^ (-(p : ℤ)) := by
  have hpfac : (0 : ℝ) < (p ! : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hCB0 : 0 ≤ CB := (norm_nonneg _).trans (hCB 0)
  have hZ : (0 : ℝ) ≤ ‖s‖ ^ (-(p : ℤ)) := zpow_nonneg (norm_nonneg _) _
  have hJ : ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
      ≤ (CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ))) := by
    calc ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
                iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
        ≤ ∫ x in Set.Ioi (0 : ℝ), ‖(bernoulliFun p (Int.fract x) : ℂ) *
                  iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (0 : ℝ), (CB * (p ! : ℝ)) * ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)) := by
          apply setIntegral_mono_on
            (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add s hs p hp).norm
            ((integrableOn_Ioi_norm_zpow_inv_add s hs p hp).const_mul _) measurableSet_Ioi
          intro x hx
          rw [iteratedDeriv_inv_add_ofReal s p (add_ofReal_ne_zero_of_re_pos hs (hx : 0 < x).le),
            norm_mul, norm_mul, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one, one_pow,
            one_mul, Complex.norm_natCast, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCB x) (by positivity))
            (zpow_nonneg (norm_nonneg _) _)
      _ = (CB * (p ! : ℝ)) * ∫ x in Set.Ioi (0 : ℝ), ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)) :=
          integral_const_mul ..
      _ ≤ (CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa [integral_Ioi_inv_one_add_sq] using integral_Ioi_norm_zpow_inv_add_le s hs p hp
  rw [digammaRemainderIoi, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast, one_div]
  calc (p ! : ℝ)⁻¹ * ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
              iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
      ≤ (p ! : ℝ)⁻¹ * ((CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ)))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = CB * (π / 2) * ‖s‖ ^ (-(p : ℤ)) := by field_simp

/-- Explicit sup bound for the Bernoulli polynomials: for `k ≥ 1` and `x ∈ [0, 1]`,
`|B_k(x)| ≤ 4 · k! / (2π)^k`. The explicit analogue of the existential bound
`exists_norm_bernoulliFun_fract_le`. -/
theorem abs_bernoulliFun_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 4 * (k ! : ℝ) / (2 * π) ^ k := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · -- `k = 1`: `B₁(x) = x - 1/2` and `1/2 ≤ 2/π`.
    have hkey : (1 : ℝ) / 2 ≤ 4 * ((1 : ℕ)! : ℝ) / (2 * π) ^ (1 : ℕ) := by
      rw [pow_one, Nat.factorial_one, Nat.cast_one, le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2]
    rw [bernoulliFun_one, abs_le]
    constructor <;> [linarith [hx.1]; linarith [hx.2]]
  replace hk : 2 ≤ k := hk
  have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  -- The dominating two-sided series `∑_{n ∈ ℤ} 1/n² = π²/3`.
  have hg : HasSum (fun n : ℤ ↦ (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 3) := by
    have h := HasSum.of_nat_of_neg (f := fun m : ℤ ↦ (1 : ℝ) / (m : ℝ) ^ 2)
      (by simpa using hasSum_zeta_two) (by simpa using hasSum_zeta_two)
    simpa [show π ^ 2 / 6 + π ^ 2 / 6 = π ^ 2 / 3 by ring] using h
  -- Pointwise domination of the Fourier summand by `1/n²`.
  have hbnd : ∀ n : ℤ, ‖(1 : ℂ) / (n : ℂ) ^ k * fourier n (x : AddCircle (1 : ℝ))‖
      ≤ (1 : ℝ) / (n : ℝ) ^ 2 := fun n ↦ by
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one, norm_div, norm_one, norm_pow,
      Complex.norm_intCast]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [zero_pow (show k ≠ 0 by lia)]
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      exact one_div_le_one_div_of_le (by positivity)
        (by rw [← sq_abs]; exact pow_le_pow_right₀ h1 hk)
  -- Take norms in the Fourier expansion: `(2π)^k/k! · |B_k(x)| ≤ ∑_{n ∈ ℤ} 1/n² = π²/3 ≤ 4`.
  have hle := (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).norm_le_of_bounded hg hbnd
  have hnorm : ‖-(2 * (π : ℂ) * Complex.I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * π) ^ k / (k ! : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow,
      show ‖2 * (π : ℂ) * Complex.I‖ = 2 * π from by simp [abs_of_pos Real.pi_pos],
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  have hπ12 : π ^ 2 / 3 ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [hnorm, div_mul_eq_mul_div, div_le_iff₀ hfac] at hle
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * π) ^ k)]
  linarith [mul_le_mul_of_nonneg_right hπ12 hfac.le]

/-- Explicit digamma remainder bound: for `Re s > 0` and `p ≥ 1`,
`‖R_p(g_s; 0, ∞)‖ ≤ p! / (2π)^(p-1) · ‖s‖^(-p)`; the Euler–Maclaurin error bound for the complex
Gamma function in logarithmic-derivative form. -/
theorem norm_digammaRemainderIoi_le' (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    ‖digammaRemainderIoi s p‖ ≤ (p ! : ℝ) / (2 * π) ^ (p - 1) * ‖s‖ ^ (-(p : ℤ)) := by
  have hπ : 0 < π := Real.pi_pos
  refine (norm_digammaRemainderIoi_le_of_bound (CB := 4 * (p ! : ℝ) / (2 * π) ^ p) hs
    hp (fun x ↦ ?_)).trans (le_of_eq ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_bernoulliFun_le hp ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  · have hpw : (2 * π) ^ p = (2 * π) ^ (p - 1) * (2 * π) := by
      conv_lhs => rw [show p = (p - 1) + 1 from by lia]
      rw [pow_succ]
    have hpwpos : (0 : ℝ) < (2 * π) ^ (p - 1) := by positivity
    rw [hpw]; field_simp; ring

end Complex.Stirling
