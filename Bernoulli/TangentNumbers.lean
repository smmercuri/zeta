/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Basic.Complex.Basic

/-!
# Tangent numbers

The *tangent numbers* `T₁, T₂, T₃, … = 1, 2, 16, 272, 7936, …` are the numerators
appearing in the Taylor expansion of the tangent function:
`tan x = ∑ₙ Tₙ · x^(2n-1) / (2n-1)!`.

The tangent numbers are *defined* here following Knuth and Buckholtz (*Math. Comp.* **21**
(1967)): the `n`-th derivative of `tan` is a polynomial in `tan`,
`dⁿ/dxⁿ tan x = Pₙ(tan x)`, where `P₀ = X` and `Pₙ₊₁ = (1 + X²)·Pₙ′`, and `Tₙ = Pₙ(0)`.

## Main definitions

* `tangentPoly`  : the tangent polynomials `Pₙ`, exactly Knuth's `P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`.
* `tangentNumber`: the `n`-th tangent number `Tₙ = P_{2n-1}(0)`; these are *positive*
                   (`tangentNumber 1 = 1, 2 = 2, 3 = 16, 4 = 272, …`).
* `tanhPoly`     : the hyperbolic analogue `Qₙ₊₁ = (1 − X²)·Qₙ′`, used to bridge to the rational
                   power series `tanhSeries`.
* `tanhSeries`   : the formal power series `tanh x = (e^{2x} - 1)/(e^{2x} + 1) ∈ ℚ⟦X⟧`,
                   the link to Mathlib's Bernoulli generating functions.

## Main results

* `derivative_tanhSeries` : the ODE `(tanh)′ = 1 − tanh²` behind the polynomial recurrence.
* `eval_tangentPoly`      : the bridge `P_{2m+1}(0) = (−1)^m · (2m+1)! · [x^{2m+1}] tanh x` linking
                            the elementary definition to the power series.
* `coeff_tanhSeries`      : the relationship to the Bernoulli numbers,
    `[x^{2m+1}] tanh x = 2^(2m+2) · (2^(2m+2) − 1) · bernoulli (2m+2) / (2m+2)!`.
* `tangentNumber_eq`      : the resulting closed form for the tangent numbers.

The power-series half of the development is over `tanh`, whose coefficients are rational, so it
lives in `ℚ⟦X⟧` beside Mathlib's Bernoulli generating functions. The substitution `x ↦ i·x` relating
`Pₙ` to the hyperbolic `Qₙ` (`map_tanhPoly`, over `ℂ[X]`) is the only place complex numbers enter.
-/
@[expose] public section


open scoped Nat

namespace TangentNumbers

noncomputable section

section Poly

open Polynomial

/-! ## The tangent polynomials `Pₙ` and the tangent numbers

The polynomial recurrence `P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`, and the tangent numbers
`Tₙ = P_{2n-1}(0)`. -/

/-- The tangent polynomials `Pₙ` (Knuth & Buckholtz, *Math. Comp.* **21** (1967)):
`P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`, so that `dⁿ/dxⁿ tan x = Pₙ(tan x)`. -/
def tangentPoly : ℕ → ℕ[X]
  | 0 => X
  | (n + 1) => (1 + X ^ 2) * derivative (tangentPoly n)

lemma tangentPoly_succ (n : ℕ) :
    tangentPoly (n + 1) = (1 + X ^ 2) * derivative (tangentPoly n) :=
  rfl

/-- The `n`-th tangent number (for `n ≥ 1`): `T₁ = 1, T₂ = 2, T₃ = 16, T₄ = 272, …`, the constant
term `P_{2n-1}(0)` of the tangent polynomial.  These are *positive*. -/
def tangentNumber (n : ℕ) : ℕ :=
  (tangentPoly (2 * n - 1)).eval 0

/-! ## The hyperbolic tangent polynomials `Qₙ`

The hyperbolic analogue `Q₀ = X`, `Qₙ₊₁ = (1 − X²)·Qₙ′`, satisfying `Dⁿ(tanh) = Qₙ(tanh)`, from
which `Qₙ(0) = n! · [xⁿ] tanh x`. -/

/-- The hyperbolic tangent polynomials: the same construction with `1 − X²` in place of
`1 + X²`, so that `dⁿ/dxⁿ tanh x = Qₙ(tanh x)`.
`Pₙ` and `Qₙ` are related by `x ↦ i·x` (see `eval_tangentPoly`). -/
def tanhPoly : ℕ → ℤ[X]
  | 0 => .X
  | (n + 1) => (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n)

private lemma tanhPoly_succ (n : ℕ) :
    tanhPoly (n + 1) = (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n) :=
  rfl

open Complex

/-- The relation `Qₙ = (−i)^{n+1} · Pₙ(i·x)` between the `tan` and `tanh` polynomials, over `ℂ`. -/
private lemma map_tanhPoly (n : ℕ) :
    (tanhPoly n).map (algebraMap ℤ ℂ) =
      C (-I ^ (n + 1)) *
        ((tangentPoly n).map (algebraMap ℕ ℂ)).comp (C I * X) := by
  induction n with
  | zero =>
    simp only [tanhPoly, tangentPoly, map_X, X_comp, zero_add, pow_one]
    rw [← mul_assoc, ← C_mul, neg_mul, I_mul_I]
    simp
  | succ n ih =>
    have hCI : C I ^ 2 = -1 := by
      rw [← C_pow, I_sq, C_neg, C_1]
    have hI : C (-I ^ (n + 2)) = C (-I ^ (n + 1)) * C I := by
      grind [C_mul, pow_succ]
    rw [tanhPoly_succ, tangentPoly_succ]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_pow, map_X, ← derivative_map, ih, derivative_comp, derivative_mul,
      derivative_C, derivative_X, mul_comp, add_comp, one_comp, pow_comp, X_comp]
    grind

end Poly

section PowerSeries

open PowerSeries

section ForMathlib

/-- The `k`-th coefficient of the `n`-th formal derivative `Dⁿ f` is `(k+1)(k+2)⋯(k+n)` times the
`(k+n)`-th coefficient of `f`. -/
private lemma coeff_iterate_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) (n k : ℕ) :
    coeff k (d⁄dX^[n] f) = (k + 1).ascFactorial n * coeff (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.ascFactorial_succ,
      ← Nat.succ_ascFactorial]
    grind

/-- The constant term of `Dⁿ f` is `n!` times the `n`-th coefficient of `f`. -/
private lemma coeff_zero_iterate {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff 0 (d⁄dX^[n] f) = n ! * coeff n f := by simpa using coeff_iterate_derivative f n 0

end ForMathlib

/-! ## The hyperbolic generating series `tanhSeries`

The power series `tanh x = (e^{2x} - 1)/(e^{2x} + 1) ∈ ℚ⟦X⟧`, its well-definedness, and the ODE
`(tanh)′ = 1 − tanh²`. -/

/-- `tanh x = (e^{2x} - 1)/(e^{2x} + 1)`, as a formal power series over `ℚ`. Its coefficients
`(2n-1)! · [x^{2n-1}] tanh x` are the tangent numbers up to sign. -/
def tanhSeries : ℚ⟦X⟧ :=
  (exp ℚ ^ 2 - 1) * (exp ℚ ^ 2 + 1)⁻¹

/-- The defining identity of `tanhSeries`, cleared of the inverse:
`tanh x · (e^{2x} + 1) = e^{2x} - 1`. -/
private lemma tanhSeries_mul_expSq_add_one :
    tanhSeries * (exp ℚ ^ 2 + 1) = exp ℚ ^ 2 - 1 := by
  simp [tanhSeries, mul_assoc, PowerSeries.inv_mul_cancel]

lemma ne_zero_of_coeff_ne_zero {R : Type*} [Semiring R] {p : R⟦X⟧} (n : ℕ) (h : p.coeff n ≠ 0) :
    p ≠ 0 := by
  grind

private lemma expSq_add_one_ne_zero : exp ℚ ^ 2 + 1 ≠ 0 :=
  ne_zero_of_coeff_ne_zero 0 (by simp)

/-- `tanh` has no constant term: `tanh 0 = 0`. -/
private lemma constantCoeff_tanhSeries : constantCoeff tanhSeries = 0 := by simp [tanhSeries]

/-- `tanhSeries` satisfies the ODE `(tanh)′ = 1 − tanh²`. -/
private lemma derivative_tanhSeries :
    d⁄dX tanhSeries = 1 - tanhSeries ^ 2 := by
  have hd : tanhSeries * (2 * (exp ℚ * exp ℚ)) + (exp ℚ ^ 2 + 1) * d⁄dX tanhSeries =
      2 * (exp ℚ * exp ℚ) := by
    simpa [derivative_exp] using congr(d⁄dX $tanhSeries_mul_expSq_add_one)
  refine mul_left_cancel₀ expSq_add_one_ne_zero ?_
  linear_combination hd - (1 - tanhSeries) * tanhSeries_mul_expSq_add_one

open scoped Polynomial

-- `aeval tanhSeries` commutes with mapping the coefficients from `ℤ` to `ℚ`.
private lemma aeval_tanhSeries_map (p : ℤ[X]) :
    Polynomial.aeval tanhSeries (p.map (algebraMap ℤ ℚ)) = Polynomial.aeval tanhSeries p :=
  (Polynomial.aeval_eq_aeval_map (by ext; simp) p tanhSeries).symm

/-- The defining property of the hyperbolic tangent polynomials at the level of power series:
`Dⁿ(tanh) = Qₙ(tanh)`. -/
private lemma iterate_derivative_tanhSeries (n : ℕ) :
    d⁄dX^[n] tanhSeries = (tanhPoly n).aeval tanhSeries := by
  induction n with
  | zero => simp [tanhPoly]
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, ← aeval_tanhSeries_map (tanhPoly n), Derivation.map_aeval, derivative_tanhSeries,
      smul_eq_mul, Polynomial.derivative_map, aeval_tanhSeries_map, tanhPoly_succ]
    simp
    ring

private lemma constantCoeff_aeval_tanhSeries (p : ℤ[X]) :
    constantCoeff (p.aeval tanhSeries) = p.eval 0 := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp [map_mul, map_pow, constantCoeff_tanhSeries]

/-- The constant term of the `n`-th hyperbolic tangent polynomial is `n!` times the `n`-th
coefficient of `tanh`:  `Qₙ(0) = n! · [xⁿ] tanh x`. -/
private lemma eval_tanhPoly (n : ℕ) :
    (tanhPoly n).eval 0 = n ! * coeff n tanhSeries := by
  rw [← constantCoeff_aeval_tanhSeries, ← coeff_zero_eq_constantCoeff_apply,
    ← iterate_derivative_tanhSeries n, coeff_zero_iterate]

/-! ## Connecting to Bernoulli -/

/-- Evaluating a mapped polynomial at `0` applies the ring map to its constant term. -/
private lemma eval_zero_map {R S : Type*} [CommSemiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (p.map f).eval 0 = f (p.eval 0) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Polynomial.coeff_zero_eq_eval_zero]

/-- The constant term of the `(2m+1)`-st tangent polynomial is the corresponding
Taylor numerator of `tan`:
`P_{2m+1}(0) = (−1)^m · (2m+1)! · [x^{2m+1}] tanh x`. -/
private lemma eval_tangentPoly (m : ℕ) :
    (tangentPoly (2 * m + 1)).eval 0 = (-1) ^ m * (2 * m + 1)! * coeff (2 * m + 1) tanhSeries := by
  -- evaluate the `ℂ[X]` relation at `0`; `eval_zero_map` + the cast lemmas turn each mapped
  -- constant term (over `ℤ` and over `ℕ`) into the matching cast, and `hI` collapses `-i^{2m+2}` to
  -- `(-1)^m`.
  have hmap := congrArg (Polynomial.eval 0) (map_tanhPoly (2 * m + 1))
  have hI : -Complex.I ^ (2 * m + 2) = (-1) ^ m := by
    have he : 2 * m + 2 = 2 * (m + 1) := by ring
    rw [he, pow_mul, Complex.I_sq]
    ring
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, eval_zero_map, eq_intCast, eq_natCast, hI] at hmap
  have hq : (tanhPoly (2 * m + 1)).eval 0
      = (-1) ^ m * (((tangentPoly (2 * m + 1)).eval 0 : ℕ) : ℚ) := mod_cast hmap
  rw [eval_tanhPoly] at hq
  rw [mul_assoc, hq, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_mul]

-- Coefficients of a power series times a numeral.
section

variable {R : Type*} [Semiring R] {p : R⟦X⟧}

@[simp] lemma coeff_mul_natCast {a k : ℕ} :
    coeff k (p * a : R⟦X⟧) = coeff k p * a := coeff_mul_C _ _ _

@[simp] lemma coeff_natCast_mul {a k : ℕ} :
    coeff k (a * p : R⟦X⟧) = a * coeff k p := coeff_C_mul _ _ _

@[simp] lemma coeff_mul_ofNat {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k (p * (ofNat(a) : R⟦X⟧)) = coeff k p * ofNat(a) := coeff_mul_C _ _ _

@[simp] lemma coeff_ofNat_mul {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k ((ofNat(a) : R⟦X⟧) * p) = ofNat(a) * coeff k p := coeff_C_mul _ _ _

end

/-- The coefficient of `x^{2m+1}` in `tanh x`, in terms of the Bernoulli numbers:
`2^(2m+2) · (2^(2m+2) - 1) · bernoulli (2m+2) / (2m+2)!`,
where `bernoulli` is Mathlib's (first) Bernoulli number. -/
theorem coeff_tanhSeries (m : ℕ) :
    coeff (2 * m + 1) tanhSeries =
      2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  -- `D` is `x·coth(x/2)`'s generating series, written via the two Bernoulli series so that
  -- its even coefficients are `2·bernoulli/(2m)!` and its odd ones vanish.
  set D := bernoulliPowerSeries ℚ + bernoulli'PowerSeries ℚ with hD
  -- the even coefficients of `D` are `2·bernoulli/(2m+2)!`.
  have hcoeffD : coeff (2 * m + 2) D = 2 * bernoulli (2 * m + 2) / (2 * m + 2)! := by
    simp [hD, map_add, bernoulliPowerSeries, bernoulli'PowerSeries]
    grind [bernoulli_eq_bernoulli'_of_ne_one]
  -- relate tanhSeries with D (and therefore with bernoulliPowerSeries)
  have main : 2 * X * tanhSeries = rescale 4 D - rescale 2 D := by
    have B3 : D * (exp ℚ - 1) = .X * (exp ℚ + 1) := by
      rw [hD, add_mul, bernoulliPowerSeries_mul_exp_sub_one,
        bernoulli'PowerSeries_mul_exp_sub_one]
      grind
    have h2 : rescale 2 D * (exp ℚ ^ 2 - 1) = 2 * .X * (exp ℚ ^ 2 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 2) B3
    have h4 : rescale 4 D * (exp ℚ ^ 4 - 1) = 4 * .X * (exp ℚ ^ 4 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 4) B3
    -- `e^{2x} ± 1` are both nonzero, so their product can be cancelled
    have hP : (exp ℚ ^ 2 + 1) * (exp ℚ ^ 2 - 1) ≠ 0 := by
      apply mul_ne_zero <;>
      · apply ne_zero_of_coeff_ne_zero 1
        simp [exp_pow_eq_rescale_exp]
    apply mul_right_cancel₀ hP
    linear_combination (2 * X * (exp ℚ ^ 2 - 1)) * tanhSeries_mul_expSq_add_one - h4 +
      (exp ℚ ^ 2 + 1) * h2
  -- Read off the coefficient of `x^{2m+2}` from the main identity.
  have hcoeff := congrArg (coeff (2 * m + 2)) main
  have lhs : coeff (2 * m + 2) (X * (2 • tanhSeries)) = 2 * coeff (2 * m + 1) tanhSeries := by simp
  have rhs : coeff (2 * m + 2) (rescale 4 D - rescale 2 D) =
      (4 ^ (2 * m + 2) - 2 ^ (2 * m + 2)) * coeff (2 * m + 2) D := by grind [coeff_rescale]
  have h4eq : (4 ^ (2 * m + 2) : ℚ) = (2 ^ (2 * m + 2)) ^ 2 := by
    have : (4 : ℚ) = 2 ^ 2 := by norm_num
    rw [this, pow_right_comm]
  grind

/-- Closed form for the tangent numbers in terms of the Bernoulli numbers:
`T_{m+1} = (-1)^m · (2m+1)! · 2^(2m+2) · (2^(2m+2) - 1) · bernoulli (2m+2) / (2m+2)!`. -/
theorem tangentNumber_eq (m : ℕ) :
    tangentNumber (m + 1) =
      (-1) ^ m * (2 * m + 1)! *
        2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  grind [tangentNumber, eval_tangentPoly, coeff_tanhSeries]

end PowerSeries

/-! ### Sanity checks: the first few tangent numbers -/

example : tangentNumber 0 = 0 := by
  simp [tangentNumber, tangentPoly]

example : tangentNumber 1 = 1 := by
  simp [tangentNumber, tangentPoly]

example : tangentNumber 2 = 2 := by
  simp [tangentNumber, tangentPoly]

example : tangentNumber 3 = 16 := by
  simp [tangentNumber, tangentPoly]

end

end TangentNumbers
