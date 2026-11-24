/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Norm

/-!
# Booker's single-pole inequality and Lehman's zero-pairing estimate

Booker's single-pole integral `∫₀² Λ(ρ) (ρ - a)/((ρ - a)² + v²) dρ` (`lem:lb_booker_single`), with
the tent `Λ(ρ) = 1 - |1 - ρ|`, and the zero-pairing estimate built from it (`lem:lb_booker`). Both
are proved with a pairing constant `c ≥ 2` free.

Two rational reformulations of the single-pole integral are set up here: the folded form
`bookerSinglePole m v` (`m = 1 - a`) and the remainder `E(m, v) = bookerRemainder m v` over the
denominator `D(τ) = bookerKernelDenom m v τ`.

## Main results

* `bookerSinglePoleIntegral_eq`: the shift/fold identity `∫₀² Λ k_a = bookerSinglePole (1 - a) v`.
* `bookerRemainder_le_of_dispersive`, `bookerSinglePoleIntegral_le_of_dispersive`: the dispersive
  régime `v² ≥ m²/3`.
* `bookerSinglePole_le_bookerSlice` (`lem:lb_P_le_slice`), `mul_bookerSlice_le`
  (`lem:ls_rung_two`): the slice domination closing the concentrated régime `v² < m²/3`.
* `bookerSinglePoleIntegral_le_of` (`lem:lb_booker_single`): `∫₀² Λ k_a ≤ c·(1-a)/((1-a)²+v²)`
  for `a ∈ [-1, 1]`, `v ≠ 0`, any `c ≥ 2`.
* `bookerPairIntegral_le_of` (`lem:lb_booker`): Lehman's zero-pairing estimate, parametric in
  `c ≥ 2`. The corollary `bookerPairIntegral_le` (`c = 5/2`) is the constant used by the
  lower-bound assembly; `bookerPairIntegral_le_two` (`c = 2`) is `lem:ls_rung_two`.
-/
@[expose] public section


/-- Denominator `D(τ) = (m² - v² - τ²)² + 4 m² v²` of the rational reduction of the single-pole
integral (`lem:lb_booker_single`). -/
def bookerKernelDenom (m v τ : ℝ) : ℝ := (m ^ 2 - v ^ 2 - τ ^ 2) ^ 2 + 4 * m ^ 2 * v ^ 2

/-- The rational remainder `E(m, v) = ∫₀¹ 2τ²(1-τ)(m² - 3v² - τ²) / D(τ) dτ` of the single-pole
integral (`lem:lb_booker_single`, equation `(⋆)`). It is read for `v ≠ 0`; at `v = 0` the
integrand develops a non-integrable singularity at `τ = m`. -/
noncomputable def bookerRemainder (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ

/-- The remainder denominator is positive for `m > 0`, `v ≠ 0`. -/
lemma bookerKernelDenom_pos {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    0 < bookerKernelDenom m v τ :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

/-- Dispersive régime (`v² ≥ m²/3`) of the single-pole bound: the rational remainder is
nonpositive (`lem:lb_booker_single`). -/
lemma bookerRemainder_nonpos_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 0 := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerRemainder, ← neg_nonneg, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_nonneg (by norm_num)
  rintro u ⟨_, hu1⟩
  rw [← neg_div]
  exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) (by linarith)) (by nlinarith [sq_nonneg u])))
    (bookerKernelDenom_pos u hm hv).le

/-- Dispersive case of the single-pole bound `(⋆)`: `E(m, v) ≤ 1/2` whenever `v² ≥ m²/3`
(`lem:lb_booker_single`). -/
lemma bookerRemainder_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 1 / 2 :=
  (bookerRemainder_nonpos_of_dispersive hm hmv).trans (by norm_num)

/-- Factorisation of the denominator `D(τ)` as the product of the two real pole denominators
`((m - τ)² + v²)` and `((m + τ)² + v²)`. -/
lemma bookerKernelDenom_eq_mul (m v τ : ℝ) :
    bookerKernelDenom m v τ = ((m - τ) ^ 2 + v ^ 2) * ((m + τ) ^ 2 + v ^ 2) := by
  unfold bookerKernelDenom; ring

/-- Partial-fraction identity underlying the rational reduction: the sum of the two real pole
kernels collapses, modulo the constant `2m/(m²+v²)`, to a single rational correction over `D`. -/
lemma bookerKernelDenom_partialFraction {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)
      = 2 * m / (m ^ 2 + v ^ 2)
        + 2 * τ ^ 2 * m * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
            / ((m ^ 2 + v ^ 2) * bookerKernelDenom m v τ) := by
  have hA : ((m - τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hB : ((m + τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
  have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
  rw [bookerKernelDenom_eq_mul]
  field_simp
  ring

/-- The folded form `P(m, v)` of Lehman's single-pole integral, the even tent weight `1 - |τ|`
folded onto `[0, 1]` (`lem:lb_booker_single`). -/
noncomputable def bookerSinglePole (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, (1 - τ) *
    ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))

/-- **Rational reduction of the single-pole integral** (`lem:lb_booker_single`, equation `(⋆)`).
`P(m, v) = m/(m²+v²) · (1 + E(m, v))`. -/
lemma bookerSinglePole_eq {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v = m / (m ^ 2 + v ^ 2) * (1 + bookerRemainder m v) := by
  have hint1 : IntervalIntegrable (fun τ : ℝ ↦ 2 * (1 - τ)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun τ : ℝ ↦ 2 * (1 - τ)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun τ : ℝ ↦
      2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by unfold bookerKernelDenom; fun_prop)
    exact fun τ ↦ (bookerKernelDenom_pos τ hm hv).ne'
  have hpt : Set.EqOn
      (fun τ : ℝ ↦ (1 - τ) *
        ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)))
      (fun τ : ℝ ↦ m / (m ^ 2 + v ^ 2) *
        (2 * (1 - τ) + 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
          / bookerKernelDenom m v τ))
      (Set.uIcc 0 1) := by
    intro τ _
    dsimp only
    have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
    have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
    rw [bookerKernelDenom_partialFraction τ hm hv]
    field_simp
  have h1 : ∫ τ in (0 : ℝ)..1, (2 : ℝ) * (1 - τ) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num
  unfold bookerSinglePole bookerRemainder
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hint1 hint2, h1]

/-- Dispersive case of the folded single-pole inequality: `P(m, v) ≤ (3/2)·m/(m²+v²)` whenever
`v² ≥ m²/3` (`lem:lb_booker_single`). -/
lemma bookerSinglePole_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerSinglePole m v ≤ 3 / 2 * (m / (m ^ 2 + v ^ 2)) := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerSinglePole_eq hm hv]
  nlinarith [mul_le_mul_of_nonneg_left (bookerRemainder_le_of_dispersive hm hmv)
    (by positivity : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2))]

/-- Integrability of `τ ↦ log(m + τ)` on `[0, 1]`. -/
private lemma intervalIntegrable_log_add_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m + τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m) (b := m + 1)).comp_add_left m
  rwa [show m - m = (0 : ℝ) by ring, show m + 1 - m = (1 : ℝ) by ring] at h

/-- Integrability of `τ ↦ log(m - τ)` on `[0, 1]`, singularity at `τ = m` (when `m ≤ 1`)
notwithstanding. -/
private lemma intervalIntegrable_log_sub_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m - τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m - 1) (b := m)).comp_sub_left m
  rw [show m - (m - 1) = (1 : ℝ) by ring, show m - m = (0 : ℝ) by ring] at h
  exact h.symm

/-- The `v = 0` slice `Φ₀(m) = (m+1)log(m+1) + (m-1)log|m-1| - 2m log m` of the folded single-pole
integral (`def:lb_slice`). The `|m - 1|` makes the definition total and continuous through
`m = 1`. -/
noncomputable def bookerSlice (m : ℝ) : ℝ :=
  (m + 1) * Real.log (m + 1) + (m - 1) * Real.log |m - 1| - 2 * m * Real.log m

/-- Integral representation of the slice (`def:lb_slice`):
`Φ₀(m) = ∫₀¹ (log(m + τ) - log(m - τ)) dτ`. -/
lemma bookerSlice_eq_integral (m : ℝ) :
    bookerSlice m = ∫ τ in (0 : ℝ)..1, (Real.log (m + τ) - Real.log (m - τ)) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_log_add_left m)
    (intervalIntegrable_log_sub_left m)]
  have e1 : (∫ τ in (0 : ℝ)..1, Real.log (m + τ))
      = (m + 1) * Real.log (m + 1) - m * Real.log m - 1 := by
    rw [intervalIntegral.integral_comp_add_left Real.log m, add_zero, integral_log]; ring
  have e2 : (∫ τ in (0 : ℝ)..1, Real.log (m - τ))
      = m * Real.log m - (m - 1) * Real.log (m - 1) - 1 := by
    rw [intervalIntegral.integral_comp_sub_left Real.log m, sub_zero, integral_log]; ring
  rw [e1, e2, bookerSlice, Real.log_abs]; ring

/-- Integration-by-parts representation of the folded single-pole integral: for `v ≠ 0`,
`P(m, v) = ½∫₀¹ log(((m + τ)² + v²)/((m - τ)² + v²)) dτ`. -/
lemma bookerSinglePole_eq_half_integral_log {m v : ℝ} (hv : v ≠ 0) :
    bookerSinglePole m v = ∫ τ in (0 : ℝ)..1,
      1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) := by
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  -- `V` is the antiderivative; its derivative is the integrand of `bookerSinglePole`.
  have hVderiv : ∀ τ : ℝ,
      HasDerivAt V ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) τ := by
    intro τ
    have hp : (m + τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hq : (m - τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hin1 : HasDerivAt (fun τ : ℝ ↦ (m + τ) ^ 2 + v ^ 2) (2 * (m + τ)) τ := by
      simpa using (((hasDerivAt_id τ).const_add m).pow 2).add_const (v ^ 2)
    have hin2 : HasDerivAt (fun τ : ℝ ↦ (m - τ) ^ 2 + v ^ 2) (2 * (m - τ) * (-1)) τ := by
      simpa using (((hasDerivAt_id τ).const_sub m).pow 2).add_const (v ^ 2)
    exact (HasDerivAt.const_mul (1 / 2) ((hin1.log hp).sub (hin2.log hq))).congr_deriv
      (by field_simp; ring)
  have hcont : Continuous
      (fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ ↦ 1 - s) (v := V) (u' := fun _ : ℝ ↦ (-1 : ℝ))
    (v' := fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))
    (fun x _ ↦ by simpa using (hasDerivAt_id x).const_sub 1) (fun x _ ↦ hVderiv x)
    (continuous_const.intervalIntegrable 0 1) (hcont.intervalIntegrable 0 1)
  have hV0 : V 0 = 0 := by simp [hVdef]
  rw [bookerSinglePole, hibp, intervalIntegral.integral_const_mul, hV0]
  ring

/-- **Monotone domination by the slice** (`lem:lb_P_le_slice`): `P(m, v) ≤ Φ₀(m)` for `m > 0`,
`v ≠ 0`. -/
lemma bookerSinglePole_le_bookerSlice {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v ≤ bookerSlice m := by
  rw [bookerSinglePole_eq_half_integral_log hv, bookerSlice_eq_integral m]
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  have hVcont : Continuous V := by
    rw [hVdef]
    exact ((Continuous.log (by fun_prop) fun τ ↦ by positivity).sub
      (Continuous.log (by fun_prop) fun τ ↦ by positivity)).const_mul _
  refine intervalIntegral.integral_mono_ae_restrict (by norm_num)
    (hVcont.intervalIntegrable 0 1)
    ((intervalIntegrable_log_add_left m).sub (intervalIntegrable_log_sub_left m)) ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) m]
    with τ hτm hτmem
  obtain ⟨hτ0, hτ1⟩ := hτmem
  have hmt : (0 : ℝ) < m + τ := by linarith
  have hmtne : m - τ ≠ 0 := sub_ne_zero.mpr fun h ↦ hτm h.symm
  have hA : (0 : ℝ) < (m + τ) ^ 2 := by positivity
  have hB : (0 : ℝ) < (m - τ) ^ 2 := by positivity
  have hAB : (m - τ) ^ 2 ≤ (m + τ) ^ 2 := by nlinarith [mul_nonneg hm.le hτ0]
  have hfrac : ((m + τ) ^ 2 + v ^ 2) / (m + τ) ^ 2 ≤ ((m - τ) ^ 2 + v ^ 2) / (m - τ) ^ 2 := by
    rw [div_le_div_iff₀ hA hB]; nlinarith [mul_le_mul_of_nonneg_left hAB (sq_nonneg v)]
  have hlog := Real.log_le_log (by positivity) hfrac
  rw [Real.log_div (by positivity) hA.ne', Real.log_div (by positivity) hB.ne',
    Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith [hlog]

/-- The single-pole integral `∫₀² Λ(ρ) (ρ - a)/((ρ - a)² + v²) dρ` of Booker's zero-pairing
estimate, with the triangular tent weight `Λ(ρ) = 1 - |1 - ρ|` (`lem:lb_booker_single`). -/
noncomputable def bookerSinglePoleIntegral (a v : ℝ) : ℝ :=
  ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2))

/-- **Shift/fold identity.** The single-pole integral equals its folded form
`bookerSinglePole (1 - a) v` (`lem:lb_booker_single`). -/
lemma bookerSinglePoleIntegral_eq {a v : ℝ} (hv : v ≠ 0) :
    bookerSinglePoleIntegral a v = bookerSinglePole (1 - a) v := by
  unfold bookerSinglePoleIntegral bookerSinglePole
  set f : ℝ → ℝ := fun ρ ↦ (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2)) with hf
  set h : ℝ → ℝ := fun τ ↦ (1 - |τ|) * ((1 - a + τ) / ((1 - a + τ) ^ 2 + v ^ 2)) with hh
  have hch : Continuous h := by
    rw [hh]
    exact Continuous.mul (by fun_prop)
      (Continuous.div (by fun_prop) (by fun_prop) fun x ↦ by positivity)
  have hcn : Continuous (fun τ ↦ h (-τ)) := hch.comp continuous_neg
  -- Step 1: shift `ρ = τ + 1`, then rewrite the integrand `f (τ + 1)` into `h`.
  have hstep : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ ρ in (0 : ℝ)..2, f ρ := by
    rw [intervalIntegral.integral_comp_add_right f 1]; norm_num
  have hcongr : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ τ in (-1 : ℝ)..1, h τ :=
    intervalIntegral.integral_congr (fun τ _ ↦ by
      simp only [hf, hh]
      rw [show (1 : ℝ) - (τ + 1) = -τ by ring, abs_neg]; ring)
  rw [← hstep, hcongr]
  -- Step 2: split `[-1, 1] = [-1, 0] ∪ [0, 1]` and reflect the left half.
  have hneg : (∫ τ in (-1 : ℝ)..0, h τ) = ∫ τ in (0 : ℝ)..1, h (-τ) := by
    rw [intervalIntegral.integral_comp_neg h]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hch.intervalIntegrable (-1) 0) (hch.intervalIntegrable 0 1), hneg,
      ← intervalIntegral.integral_add (hcn.intervalIntegrable 0 1) (hch.intervalIntegrable 0 1)]
  -- Step 3: identify the folded integrand with `bookerSinglePole`'s.
  refine intervalIntegral.integral_congr (fun τ hτ ↦ ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  obtain ⟨hτ0, _⟩ := hτ
  simp only [hh, abs_neg, abs_of_nonneg hτ0]
  ring

/-- Dispersive case of the single-pole inequality (`lem:lb_booker_single`): for `a < 1` and
`v² ≥ (1-a)²/3`, the single-pole integral is bounded by `(3/2)·(1-a)/((1-a)²+v²)`. -/
lemma bookerSinglePoleIntegral_le_of_dispersive {a v : ℝ} (ha : a < 1)
    (hav : (1 - a) ^ 2 ≤ 3 * v ^ 2) :
    bookerSinglePoleIntegral a v ≤ 3 / 2 * ((1 - a) / ((1 - a) ^ 2 + v ^ 2)) := by
  have hv : v ≠ 0 := by
    rintro rfl; nlinarith [sub_pos.mpr ha, mul_pos (sub_pos.mpr ha) (sub_pos.mpr ha)]
  rw [bookerSinglePoleIntegral_eq hv]
  exact bookerSinglePole_le_of_dispersive (by linarith) hav

open intervalIntegral MeasureTheory Topology in
/-- **Tent-folding identity.** The double integral of `f (r + σ)` over the unit square equals the
integral of `f` over `[0, 2]` weighted by the triangular tent `1 - |1 - ρ|`. -/
lemma intervalIntegral.integral_integral_add_eq_tent {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ := by
  -- `F` and `G` are the first and second antiderivatives of `f` based at `0`; note `G 0 = 0`.
  set F : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, f t with hF_def
  have hFderiv : ∀ x : ℝ, HasDerivAt F (f x) x := fun x ↦
    integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
      (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
  have hFcont : Continuous F := Differentiable.continuous fun x ↦ (hFderiv x).differentiableAt
  set G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, F t with hG_def
  have e0 : (∫ σ in (0 : ℝ)..1, F σ) = G 1 := by simp only [hG_def]
  have hFG2 : (∫ ρ in (1 : ℝ)..2, F ρ) = G 2 - G 1 := by
    simp only [hG_def]
    linarith [integral_add_adjacent_intervals (hFcont.intervalIntegrable (μ := volume) 0 1)
      (hFcont.intervalIntegrable 1 2)]
  -- left-hand side: the inner integral telescopes to `F (1 + σ) - F σ`.
  have hinner : ∀ σ : ℝ, (∫ r in (0 : ℝ)..1, f (r + σ)) = F (1 + σ) - F σ := fun σ ↦ by
    rw [integral_comp_add_right f σ, zero_add]
    simp only [hF_def]
    linarith [integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) 0 σ)
      (hf.intervalIntegrable σ (1 + σ))]
  have e1 : (∫ σ in (0 : ℝ)..1, F (1 + σ)) = G 2 - G 1 := by
    rw [integral_congr (g := fun σ ↦ F (σ + 1)) fun σ _ ↦ by rw [add_comm],
      integral_comp_add_right F 1, zero_add, (by norm_num : (1 : ℝ) + 1 = 2), hFG2]
  have hc1 : IntervalIntegrable (fun σ : ℝ ↦ F (1 + σ)) volume 0 1 :=
    (hFcont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  have hLHS : (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ)) = G 2 - 2 * G 1 := by
    rw [integral_congr (fun σ _ ↦ hinner σ),
      integral_sub hc1 (hFcont.intervalIntegrable 0 1), e1, e0]
    ring
  -- right-hand side, via integration by parts on each half of the tent
  have htent : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * f ρ) := by fun_prop
  have hsplit : (∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ)
      = (∫ ρ in (0 : ℝ)..1, ρ * f ρ) + ∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ := by
    rw [← integral_add_adjacent_intervals (htent.intervalIntegrable 0 1)
      (htent.intervalIntegrable 1 2)]
    congr 1
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hρ
      rw [abs_of_nonneg (by linarith [hρ.2] : (0 : ℝ) ≤ 1 - ρ)]; ring
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hρ
      rw [abs_of_nonpos (by linarith [hρ.1] : 1 - ρ ≤ 0)]; ring
  have hIBP1 : (∫ ρ in (0 : ℝ)..1, ρ * f ρ) = F 1 - G 1 := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (u := fun ρ ↦ ρ) (v := F) (u' := fun _ ↦ (1 : ℝ)) (v' := f)
      (fun x _ ↦ hasDerivAt_id x) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 0 1) (hf.intervalIntegrable 0 1)
    simp only [one_mul, zero_mul, sub_zero] at h ⊢
    rw [h, e0]
  have hIBP2 : (∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ) = -F 1 + (G 2 - G 1) := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := 2)
      (u := fun ρ ↦ 2 - ρ) (v := F) (u' := fun _ ↦ (-1 : ℝ)) (v' := f)
      (fun x _ ↦ (hasDerivAt_id x).const_sub 2) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 1 2) (hf.intervalIntegrable 1 2)
    beta_reduce at h
    rw [h, show (∫ x in (1 : ℝ)..2, (-1 : ℝ) * F x) = -(G 2 - G 1) from by
      rw [intervalIntegral.integral_const_mul, hFG2]; ring]
    ring
  rw [hLHS, hsplit, hIBP1, hIBP2]
  ring

open intervalIntegral MeasureTheory in
/-- Reduction step of the scalar pairing inequality (`lem:lb_booker_scalar`): the kernel double
integral over the unit square splits into the two single-pole integrals
`bookerSinglePoleIntegral (-u) v` and `bookerSinglePoleIntegral u v`. -/
lemma integral_integral_eq_bookerSinglePoleIntegral_add {u v : ℝ} (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
  have habs : Continuous (fun ρ : ℝ ↦ 1 - |1 - ρ|) := by fun_prop
  have hcont : Continuous (fun s : ℝ ↦
      (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity))
  have hk1 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - -u) / ((ρ - -u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  have hk2 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - u) / ((ρ - u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  calc (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) *
          ((ρ + u) / ((ρ + u) ^ 2 + v ^ 2) + (ρ - u) / ((ρ - u) ^ 2 + v ^ 2)) :=
        intervalIntegral.integral_integral_add_eq_tent hcont
    _ = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
        unfold bookerSinglePoleIntegral
        rw [← integral_add (hk1.intervalIntegrable 0 2) (hk2.intervalIntegrable 0 2)]
        refine integral_congr (fun ρ _ ↦ ?_)
        ring

/-- The reciprocal slice `L(x) = (x+1)log(x+1) - (x-1)log|x-1|` (`def:lb_slice_recip`), the
`x = 1/m` transform of `bookerSlice`. -/
noncomputable def bookerSliceReciprocal (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - (x - 1) * Real.log |x - 1|

/-- Abs-free form of the reciprocal slice. -/
lemma bookerSliceReciprocal_eq_sub (x : ℝ) :
    bookerSliceReciprocal x = (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) := by
  rw [bookerSliceReciprocal, Real.log_abs]

/-- Derivative of `y ↦ log (y + 1)` off its singularity. -/
private lemma hasDerivAt_log_add_one {x : ℝ} (h : x + 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y + 1)) (x + 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).add_const 1)

/-- Derivative of `y ↦ log (y - 1)` off its singularity. -/
private lemma hasDerivAt_log_sub_one {x : ℝ} (h : x - 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y - 1)) (x - 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).sub_const 1)

/-- Derivative of the reciprocal slice off the singularities `x = ±1`:
`L'(x) = log(x+1) - log(x-1)`. -/
private lemma hasDerivAt_bookerSliceReciprocal {x : ℝ} (h1 : x + 1 ≠ 0) (h2 : x - 1 ≠ 0) :
    HasDerivAt bookerSliceReciprocal (Real.log (x + 1) - Real.log (x - 1)) x := by
  rw [funext bookerSliceReciprocal_eq_sub]
  have d1 : HasDerivAt (fun x : ℝ ↦ x + 1) 1 x := (hasDerivAt_id x).add_const 1
  have d2 : HasDerivAt (fun x : ℝ ↦ x - 1) 1 x := (hasDerivAt_id x).sub_const 1
  exact ((d1.mul (hasDerivAt_log_add_one h1)).sub (d2.mul (hasDerivAt_log_sub_one h2))).congr_deriv
    (by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]; ring)

/-- On any open set avoiding the singularities, `deriv L` agrees with `x ↦ log(x+1) - log(x-1)` on a
neighbourhood of each point. -/
private lemma deriv_bookerSliceReciprocal_eqOn {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv bookerSliceReciprocal =ᶠ[nhds x] fun y ↦ Real.log (y + 1) - Real.log (y - 1) :=
  Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦
    (hasDerivAt_bookerSliceReciprocal (hUmem y hy).1 (hUmem y hy).2).deriv

/-- `deriv L` is itself differentiable off the singularities, with `deriv (deriv L) x =
(x+1)⁻¹ - (x-1)⁻¹`. -/
private lemma hasDerivAt_deriv_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (deriv bookerSliceReciprocal) ((x + 1)⁻¹ - (x - 1)⁻¹) x := by
  have heq := deriv_bookerSliceReciprocal_eqOn hU hUmem hx
  exact (((hasDerivAt_log_add_one (hUmem x hx).1).sub
    (hasDerivAt_log_sub_one (hUmem x hx).2)).congr_of_eventuallyEq heq)

/-- Second derivative of the reciprocal slice off the singularities:
`L''(x) = (x+1)⁻¹ - (x-1)⁻¹ = -2/(x²-1)`. -/
private lemma deriv2_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv^[2] bookerSliceReciprocal x = (x + 1)⁻¹ - (x - 1)⁻¹ := by
  change deriv (deriv bookerSliceReciprocal) x = _
  exact (hasDerivAt_deriv_bookerSliceReciprocal hU hUmem hx).deriv

/-- Continuity of the abs-free reciprocal slice, through `x = ±1` included. -/
private lemma continuous_bookerSliceReciprocal_form :
    Continuous fun x : ℝ ↦ (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) :=
  (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x + 1)).sub
    (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x - 1))

/-- The reciprocal slice `L` is continuous on every set. -/
private lemma continuousOn_bookerSliceReciprocal (S : Set ℝ) :
    ContinuousOn bookerSliceReciprocal S :=
  continuous_bookerSliceReciprocal_form.continuousOn.congr fun x _ ↦
    bookerSliceReciprocal_eq_sub x

/-- `L` is convex on `[1/2, 1]`. -/
private lemma convexOn_bookerSliceReciprocal :
    ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioo (1 / 2 : ℝ) 1, y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by linarith [hy.1]), ne_of_lt (by linarith [hy.2])⟩
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioo hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioo hUmem hx]
    have hna : (x - 1)⁻¹ < 0 := inv_lt_zero.mpr (by linarith [hx.2])
    have hpb : (0 : ℝ) < (x + 1)⁻¹ := inv_pos.mpr (by linarith [hx.1])
    linarith

/-- `L` is concave on `[1, ∞)`. -/
private lemma concaveOn_bookerSliceReciprocal :
    ConcaveOn ℝ (Set.Ici (1 : ℝ)) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioi (1 : ℝ), y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith),
      ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith)⟩
  apply concaveOn_of_deriv2_nonpos (convex_Ici _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioi hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioi hUmem hx, sub_nonpos]
    simp only [Set.mem_Ioi] at hx
    have ha : 0 < x - 1 := by linarith
    exact inv_anti₀ ha (by linarith)

/-- **A concave function lies below each of its tangent lines**: if `f` is concave on `S`,
`x₀ ∈ S` and `HasDerivAt f f' x₀`, then `f x ≤ f x₀ + f' (x - x₀)` for every `x ∈ S`. -/
private lemma le_add_deriv_mul_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} {x x₀ f' : ℝ}
    (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (hx₀ : x₀ ∈ S) (hd : HasDerivAt f f' x₀) :
    f x ≤ f x₀ + f' * (x - x₀) := by
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · have hslope := hf.le_slope_of_hasDerivAt hx hx₀ hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith : (0 : ℝ) < x₀ - x)] at hslope
    nlinarith [hslope]
  · rw [heq]; simp
  · have hslope := hf.slope_le_of_hasDerivAt hx₀ hx hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith : (0 : ℝ) < x - x₀)] at hslope
    nlinarith [hslope]

/-- **Affine bound on the reciprocal slice** (`lem:ls_rung_two`): `L(x) ≤ (3/2) x²` for `x ≥ 1/2`.
The constant `3/2` is close to the true supremum `sup_x L(x)/x² = 1.4794…`, so the margin is only
`≈ 0.02`. -/
lemma bookerSliceReciprocal_le {x : ℝ} (hx : 1 / 2 ≤ x) :
    bookerSliceReciprocal x ≤ 3 / 2 * x ^ 2 := by
  have hl2l := Real.log_two_gt_d9
  have hl2u := Real.log_two_lt_d9
  have hl3l := Real.log_three_gt_d9
  have hl3u := Real.log_three_lt_d9
  have hl5l := Real.log_five_gt_d9
  have hl5u := Real.log_five_lt_d9
  rcases le_total x 1 with hx1 | hx1
  · -- Convex piece `x ∈ [1/2, 1]`: secant chord through `(1/2, L(1/2))` and `(1, L(1))`.
    have hmem_half : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have hmem_one : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have ha : (0 : ℝ) ≤ 2 * (1 - x) := by linarith
    have hb : (0 : ℝ) ≤ 2 * x - 1 := by linarith
    have hab : 2 * (1 - x) + (2 * x - 1) = 1 := by ring
    have hchord := convexOn_bookerSliceReciprocal.2 hmem_half hmem_one ha hb hab
    simp only [smul_eq_mul] at hchord
    rw [show 2 * (1 - x) * (1 / 2) + (2 * x - 1) * 1 = x by ring] at hchord
    have e_half : bookerSliceReciprocal (1 / 2) = 3 / 2 * Real.log 3 - 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show |(1 : ℝ) / 2 - 1| = 1 / 2 by
          rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, abs_neg]; norm_num,
        show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one]
      ring
    have e_one : bookerSliceReciprocal 1 = 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
      simp only [abs_zero, Real.log_zero, mul_zero, sub_zero]
    rw [e_half, e_one] at hchord
    nlinarith [hchord, sq_nonneg (x - (8 * Real.log 2 - 3 * Real.log 3) / 3),
      hl2l, hl2u, hl3l, hl3u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 3 - 1.0986122885)
        (by linarith : (0 : ℝ) ≤ (0.6931471808 : ℝ) - Real.log 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803)
        (by linarith : (0 : ℝ) ≤ (1.0986122888 : ℝ) - Real.log 3)]
  · -- Concave piece `x ∈ [1, ∞)`: tangent line at `x₀ = 13/12`, slope `2 log 5`.
    have hx0mem : (13 / 12 : ℝ) ∈ Set.Ici (1 : ℝ) := by norm_num
    have hxmem : x ∈ Set.Ici (1 : ℝ) := hx1
    have hderiv : HasDerivAt bookerSliceReciprocal
        (Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1)) (13 / 12) :=
      hasDerivAt_bookerSliceReciprocal (by norm_num) (by norm_num)
    have eL' : Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1) = 2 * Real.log 5 := by
      rw [show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num, show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        ← Real.log_div (by norm_num) (by norm_num),
        show (25 : ℝ) / 12 / (1 / 12) = 25 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.log_pow]
      push_cast; ring
    have eL0 : bookerSliceReciprocal (13 / 12)
        = 25 / 6 * Real.log 5 - 4 * Real.log 2 - 2 * Real.log 3 := by
      rw [bookerSliceReciprocal_eq_sub, show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num,
        show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one, show (25 : ℝ) = 5 ^ 2 by norm_num, show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
        Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      push_cast; ring
    rw [eL'] at hderiv
    have htan : bookerSliceReciprocal x
        ≤ bookerSliceReciprocal (13 / 12) + 2 * Real.log 5 * (x - 13 / 12) :=
      le_add_deriv_mul_of_concaveOn concaveOn_bookerSliceReciprocal hxmem hx0mem hderiv
    rw [eL0] at htan
    nlinarith [htan, sq_nonneg (x - 2 * Real.log 5 / 3), hl2l, hl2u, hl3l, hl5l, hl5u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 5 - 1.6094379123)
        (by linarith : (0 : ℝ) ≤ (1.6094379126 : ℝ) - Real.log 5)]

/-- Reciprocal identity for the slice (`lem:lb_slice_recip_eq`): `Φ₀(m) = m L(1/m)` for
`m > 0`. -/
lemma bookerSlice_eq_mul_bookerSliceReciprocal {m : ℝ} (hm : 0 < m) :
    bookerSlice m = m * bookerSliceReciprocal (1 / m) := by
  have hm0 : m ≠ 0 := hm.ne'
  rcases eq_or_ne m 1 with rfl | hm1
  · norm_num [bookerSlice, bookerSliceReciprocal]
  · have hlm : Real.log (1 / m + 1) = Real.log (m + 1) - Real.log m := by
      rw [show (1 : ℝ) / m + 1 = (m + 1) / m by field_simp; ring, Real.log_div (by positivity) hm0]
    have habs : |m - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hm1)
    have hlm2 : Real.log |1 / m - 1| = Real.log |m - 1| - Real.log m := by
      rw [show |(1 : ℝ) / m - 1| = |m - 1| / m by
            rw [show (1 : ℝ) / m - 1 = (1 - m) / m by field_simp, abs_div, abs_of_pos hm,
              abs_sub_comm],
        Real.log_div habs hm0]
    rw [bookerSlice, bookerSliceReciprocal, hlm, hlm2]
    field_simp
    ring

/-- **One-variable slice bound** (`lem:ls_rung_two`): `m Φ₀(m) ≤ 3/2` for `m ∈ (0, 2]`. -/
lemma mul_bookerSlice_le {m : ℝ} (hm0 : 0 < m) (hm2 : m ≤ 2) :
    m * bookerSlice m ≤ 3 / 2 := by
  have hx : (1 : ℝ) / 2 ≤ 1 / m := by rw [le_div_iff₀ hm0]; linarith
  rw [bookerSlice_eq_mul_bookerSliceReciprocal hm0]
  nlinarith [mul_le_mul_of_nonneg_left (bookerSliceReciprocal_le hx) (sq_nonneg m),
    (by field_simp : m ^ 2 * (1 / m) ^ 2 = 1)]

/-- **Folded form of Booker's single-pole bound**, parametric in the pairing constant `c ≥ 2`:
for `m ∈ [0, 2]` and `v ≠ 0`, `P(m, v) ≤ c·m/(m² + v²)` (`lem:lb_booker_single`,
`lem:ls_rung_two`). The threshold `c = 2` is sharp for this argument: it is attained at the sector
boundary `3v² = m²`. -/
lemma bookerSinglePole_le_of {m v : ℝ} (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePole m v ≤ c * (m / (m ^ 2 + v ^ 2)) := by
  rcases hm0.lt_or_eq with hm | rfl
  · rcases le_or_gt (m ^ 2) (3 * v ^ 2) with hd | hconc
    · -- Dispersive régime `m² ≤ 3v²`: the `3/2` bound is a fortiori `≤ c` since `m/(m²+v²) ≥ 0`.
      have hdisp := bookerSinglePole_le_of_dispersive hm hd
      have hpos : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2) := by positivity
      exact le_trans hdisp (mul_le_mul_of_nonneg_right (by linarith) hpos)
    · -- Concentrated régime `3v² < m²`: bound `P` by the slice.
      have hP : bookerSinglePole m v ≤ bookerSlice m := bookerSinglePole_le_bookerSlice hm hv
      have hΦ : m * bookerSlice m ≤ 3 / 2 := mul_bookerSlice_le hm hm2
      have hmv2 : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
      have hB : bookerSlice m ≤ 3 / (2 * m) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)]; nlinarith [hΦ]
      have hD : (3 : ℝ) / (2 * m) ≤ c * (m / (m ^ 2 + v ^ 2)) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m),
          show c * (m / (m ^ 2 + v ^ 2)) * (2 * m) = 2 * c * m ^ 2 / (m ^ 2 + v ^ 2) by ring,
          le_div_iff₀ hmv2]
        nlinarith [hconc.le, mul_nonneg (show (0 : ℝ) ≤ c - 2 by linarith) (mul_pos hm hm).le]
      exact le_trans (le_trans hP hB) hD
  · -- `m = 0`: the integrand vanishes identically and both sides are `0`.
    have h0 : bookerSinglePole 0 v = 0 := by
      rw [bookerSinglePole, intervalIntegral.integral_congr (g := fun _ : ℝ ↦ (0 : ℝ))
        (fun τ _ ↦ by
          rw [show (0 : ℝ) + τ = τ by ring, show (0 : ℝ) - τ = -τ by ring, neg_sq]; ring),
        intervalIntegral.integral_zero]
    rw [h0]
    simp

/-- The `c = 5/2` case of `bookerSinglePole_le_of`. -/
lemma bookerSinglePole_le {m v : ℝ} (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hv : v ≠ 0) :
    bookerSinglePole m v ≤ 5 / 2 * (m / (m ^ 2 + v ^ 2)) :=
  bookerSinglePole_le_of hm0 hm2 hv (by norm_num)

/-- **Booker's single-pole inequality** (`lem:lb_booker_single`), parametric in the pairing
constant `c ≥ 2`: for `a ∈ [-1, 1]` and `v ≠ 0`,
`∫₀² Λ(ρ) (ρ - a)/((ρ - a)² + v²) dρ ≤ c·(1 - a)/((1 - a)² + v²)`. -/
theorem bookerSinglePoleIntegral_le_of {a v : ℝ} (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePoleIntegral a v ≤ c * ((1 - a) / ((1 - a) ^ 2 + v ^ 2)) := by
  rw [bookerSinglePoleIntegral_eq hv]
  exact bookerSinglePole_le_of (by linarith) (by linarith) hv hc

/-- The `c = 5/2` case of `bookerSinglePoleIntegral_le_of`. -/
theorem bookerSinglePoleIntegral_le {a v : ℝ} (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hv : v ≠ 0) :
    bookerSinglePoleIntegral a v ≤ 5 / 2 * ((1 - a) / ((1 - a) ^ 2 + v ^ 2)) :=
  bookerSinglePoleIntegral_le_of ha1 ha2 hv (by norm_num)

/-- The paired single-pole kernel `ψ(s) = (s+u)/((s+u)²+v²) + (s-u)/((s-u)²+v²)` of Lehman's
zero-pairing estimate (`lem:lb_booker`). -/
noncomputable def bookerPairKernel (u v s : ℝ) : ℝ :=
  (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)

/-- Booker's paired log-modulus integral
`∫₀^d log |((x+d+w)(x+d-w̄)) / ((x+w)(x-w̄))| dx`, the left-hand side of Lehman's zero-pairing
estimate (`lem:lb_booker`). -/
noncomputable def bookerPairIntegral (d : ℝ) (w : ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..d, Real.log ‖((x : ℂ) + (d : ℂ) + w) *
    ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
    (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖

/-- **Scalar pairing inequality** (`lem:lb_booker_scalar`), parametric in the pairing constant
`c ≥ 2`: for `u ∈ [0, 1]` and `v ≠ 0`, with `ψ = bookerPairKernel u v`,
`∬_{[0,1]²} ψ(r + σ) dr dσ ≤ c ψ(1)`. -/
theorem bookerPairKernel_integral_le_of {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (r + σ))
      ≤ c * bookerPairKernel u v 1 := by
  unfold bookerPairKernel
  rw [integral_integral_eq_bookerSinglePoleIntegral_add hv]
  have h1 := bookerSinglePoleIntegral_le_of (a := -u) (v := v) (by linarith) (by linarith) hv hc
  have h2 := bookerSinglePoleIntegral_le_of (a := u) (v := v) (by linarith) (by linarith) hv hc
  simp only [sub_neg_eq_add] at h1
  rw [mul_add]
  linarith

/-- The `c = 5/2` case of `bookerPairKernel_integral_le_of`. -/
theorem bookerPairKernel_integral_le {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (r + σ))
      ≤ 5 / 2 * bookerPairKernel u v 1 :=
  bookerPairKernel_integral_le_of hu0 hu1 hv (by norm_num)

/-- The kernel `ψ` is even in the pole offset `u`, so its value at `u` equals its value at `|u|`. -/
private lemma bookerPairKernel_abs (u v s : ℝ) :
    bookerPairKernel u v s = bookerPairKernel |u| v s := by
  unfold bookerPairKernel
  rcases abs_choice u with h | h
  · rw [h]
  · rw [h]; ring

/-- Degree `(-1)` homogeneity of the kernel: `ψ_{u,v}(d·s) = (1/d)·ψ_{u/d,v/d}(s)`. -/
private lemma bookerPairKernel_scale (u v s d : ℝ) (hd : d ≠ 0) (hv : v ≠ 0) :
    bookerPairKernel u v (d * s) = 1 / d * bookerPairKernel (u / d) (v / d) s := by
  have h1 : (d * s + u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h2 : (d * s - u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h3 : (s + u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  have h4 : (s - u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  unfold bookerPairKernel
  rw [show d * s + u = d * (s + u / d) by field_simp,
    show d * s - u = d * (s - u / d) by field_simp]
  field_simp

/-- The logarithm of a complex norm as half the logarithm of the squared modulus. -/
private lemma Complex.log_norm_eq_half_log (z : ℂ) :
    Real.log ‖z‖ = 1 / 2 * Real.log (z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply, ← sq, ← sq]
  ring

/-- The single-pole kernel `(x+σ+b)/((x+σ+b)²+v²)` integrated in `σ`; the antiderivative is
`½ log((x+σ+b)²+v²)`. -/
private lemma integral_pole_add (x d v b : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ + b) / ((x + σ + b) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d + b) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x + b) ^ 2 + v ^ 2) := by
  have hpos : ∀ s : ℝ, (0 : ℝ) < (x + s + b) ^ 2 + v ^ 2 := fun s ↦ by positivity
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) d,
      HasDerivAt (fun y ↦ 1 / 2 * Real.log ((x + y + b) ^ 2 + v ^ 2))
        ((x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) s := by
    intro s _
    have hlin : HasDerivAt (fun y ↦ x + y + b) 1 s := by
      simpa using ((hasDerivAt_id s).const_add x).add_const b
    have hsq : HasDerivAt (fun y ↦ (x + y + b) ^ 2 + v ^ 2) (2 * (x + s + b)) s := by
      simpa using (hlin.pow 2).add_const (v ^ 2)
    exact ((hsq.log (hpos s).ne').const_mul (1 / 2)).congr_deriv (by ring)
  have hcont : Continuous (fun s ↦ (x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ ne_of_gt (hpos s))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]; norm_num

/-- The subtraction variant of `integral_pole_add`, obtained by `b ↦ -a`. -/
private lemma integral_pole_sub (x d v a : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d - a) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x - a) ^ 2 + v ^ 2) := by
  rw [show (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
        = ∫ σ in (0 : ℝ)..d, (x + σ + (-a)) / ((x + σ + (-a)) ^ 2 + v ^ 2) from
      intervalIntegral.integral_congr (fun σ _ ↦ by ring_nf), integral_pole_add x d v (-a) hv]
  ring_nf

/-- Rescaling of the kernel double integral from `[0,d]²` to the unit square `[0,1]²`. -/
private lemma double_integral_bookerPairKernel_scale {d u v : ℝ} (hd : 0 < d) (hv : v ≠ 0) :
    (∫ x in (0 : ℝ)..d, ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))
      = d * ∫ x in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (x + σ) := by
  have subst : ∀ (f : ℝ → ℝ), (∫ y in (0 : ℝ)..d, f y) = d * ∫ y in (0 : ℝ)..1, f (d * y) := by
    intro f
    rw [intervalIntegral.integral_comp_mul_left f hd.ne', mul_zero, mul_one, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  rw [subst (fun x ↦ ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ d * ∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        (fun y _ ↦ subst (fun σ ↦ bookerPairKernel u v (d * y + σ)))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ))
        (fun y _ ↦ ?_)]
  · rw [intervalIntegral.integral_const_mul]; field_simp
  · change (∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        = 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun σ _ ↦ ?_)
    rw [show d * y + d * σ = d * (y + σ) by ring, bookerPairKernel_scale u v (y + σ) d hd.ne' hv]

/-- Signed form of the scalar pairing inequality `bookerPairKernel_integral_le_of`, valid for
`|u| ≤ 1` and any `c ≥ 2`. The kernel's evenness in `u` reduces it to the `u ≥ 0` case. -/
private lemma bookerPairKernel_integral_le_of_abs_le {u v : ℝ} (hu : |u| ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
      ≤ c * bookerPairKernel u v 1 := by
  have key := bookerPairKernel_integral_le_of (abs_nonneg u) hu hv hc
  rw [show (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
        = ∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel |u| v (r + σ) from
      intervalIntegral.integral_congr (fun σ _ ↦
        intervalIntegral.integral_congr (fun r _ ↦ by
          rw [bookerPairKernel_abs u v (σ + r), add_comm σ r]))]
  rw [bookerPairKernel_abs u v 1]
  exact key

/-- **Lehman's zero-pairing estimate** (`lem:lb_booker`), parametric in the pairing constant
`c ≥ 2`: for `d > 1/2` and `w ∈ ℂ` with `|Re w| ≤ 1/2` and `Im w ≠ 0`,
`bookerPairIntegral d w ≤ c d² Re(1/(d+w) + 1/(d-w̄))`. -/
theorem bookerPairIntegral_le_of {d : ℝ} (hd1 : 1 / 2 < d) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) (hwim : w.im ≠ 0) {c : ℝ} (hc : 2 ≤ c) :
    bookerPairIntegral d w
      ≤ c * d ^ 2 * (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re := by
  unfold bookerPairIntegral
  have hd0 : 0 < d := by linarith
  have hre : (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re
      = bookerPairKernel w.re w.im d := by
    unfold bookerPairKernel
    simp only [Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, one_div]
    ring
  have hint : ∀ x : ℝ,
      Real.log ‖((x : ℂ) + (d : ℂ) + w) * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
        (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖
        = ∫ σ in (0 : ℝ)..d, bookerPairKernel w.re w.im (x + σ) := by
    intro x
    have hz : ∀ z : ℂ, z.im ≠ 0 → z ≠ 0 := fun z hz h ↦ hz (by rw [h]; simp)
    have hA : ((x : ℂ) + (d : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hB : ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    have hC : ((x : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hD : ((x : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    rw [norm_div, norm_mul, norm_mul,
        Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB))
                     (mul_ne_zero (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD)),
        Real.log_mul (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB),
        Real.log_mul (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD),
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log,
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    unfold bookerPairKernel
    rw [intervalIntegral.integral_add, integral_pole_add x d w.im w.re hwim,
        integral_pole_sub x d w.im w.re hwim]
    · ring_nf
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
  rw [hre, intervalIntegral.integral_congr (fun x _ ↦ hint x),
      double_integral_bookerPairKernel_scale hd0 hwim]
  have hRHS : c * d ^ 2 * bookerPairKernel w.re w.im d
      = d * (c * bookerPairKernel (w.re / d) (w.im / d) 1) := by
    have hs := bookerPairKernel_scale w.re w.im 1 d hd0.ne' hwim
    rw [mul_one] at hs
    rw [hs]; field_simp
  rw [hRHS]
  apply mul_le_mul_of_nonneg_left _ hd0.le
  refine bookerPairKernel_integral_le_of_abs_le ?_ ?_ hc
  · rw [abs_div, abs_of_pos hd0, div_le_one hd0]; linarith
  · exact div_ne_zero hwim hd0.ne'

/-- The `c = 5/2` case of `bookerPairIntegral_le_of`, the constant used by the lower-bound
assembly. -/
theorem bookerPairIntegral_le {d : ℝ} (hd1 : 1 / 2 < d) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) (hwim : w.im ≠ 0) :
    bookerPairIntegral d w
      ≤ 5 / 2 * d ^ 2 * (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re :=
  bookerPairIntegral_le_of hd1 hw hwim (by norm_num)

/-- The zero-pairing estimate at the pairing constant `c = 2` (`lem:ls_rung_two`). -/
theorem bookerPairIntegral_le_two {d : ℝ} (hd1 : 1 / 2 < d) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) (hwim : w.im ≠ 0) :
    bookerPairIntegral d w
      ≤ 2 * d ^ 2 * (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re :=
  bookerPairIntegral_le_of hd1 hw hwim le_rfl

