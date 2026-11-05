/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
public import Zeta.EulerMaclaurin.Continuation

/-!
# Non-vanishing of `ζ` on the real axis away from the trivial zeros

The Riemann zeta function has no zeros on the real line other than the trivial zeros
`-2, -4, -6, …`. This is what lets the real axis be included in a Riemann-hypothesis statement
(cf. mathlib's `RiemannHypothesis`, which excludes the trivial zeros via
`¬∃ n : ℕ, s = -2 * (n + 1)`).

## Main results

- `riemannZeta_ne_zero_of_mem_Ioo_zero_one`: `ζ ≠ 0` on the real segment `(0, 1)`.
- `riemannZeta_ofReal_ne_zero`: `ζ` has no non-trivial real zeros.
-/
@[expose] public section


open Set

/-- **ζ does not vanish on the real segment `(0, 1)`.** -/
theorem riemannZeta_ne_zero_of_mem_Ioo_zero_one {x : ℝ} (hx : x ∈ Ioo 0 1) :
    riemannZeta x ≠ 0 :=
  fun hz ↦ by simpa [hz] using riemannZeta_ofReal_re_neg_of_mem_Ioo hx

/-- **ζ has no non-trivial real zeros.** For real `x` that is not a trivial zero `-2(n+1)`,
`ζ(x) ≠ 0`. -/
theorem riemannZeta_ofReal_ne_zero {x : ℝ} (h : ¬∃ n : ℕ, x = -2 * (n + 1)) :
    riemannZeta x ≠ 0 := by
  by_cases hx1 : 1 ≤ x
  · -- `x ≥ 1`: `ζ ≠ 0` on `Re ≥ 1`.
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hx1)
  push Not at hx1
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · -- `x < 0`: reflect to `w = 1 - x` (so `Re w ≥ 1`) and apply the functional-equation
    -- non-vanishing `Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re`, leaving only the cosine
    -- factor, which vanishes exactly at the trivial zeros.
    rw [show (x : ℂ) = 1 - ((1 - x : ℝ) : ℂ) by push_cast; ring]
    refine Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re
      (by simp only [Complex.ofReal_re]; linarith) ?_
    rw [show ((Real.pi : ℂ) * ((1 - x : ℝ) : ℂ) / 2) = ((Real.pi * (1 - x) / 2 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_cos, ne_eq, Complex.ofReal_eq_zero]
    intro hcos
    rw [Real.cos_eq_zero_iff] at hcos
    obtain ⟨n, hn⟩ := hcos
    apply h
    have hpi := Real.pi_pos
    have hxn : x = -2 * n := by field_simp at hn; nlinarith [hn]
    have hn1 : (0 : ℤ) < n := by exact_mod_cast show (0 : ℝ) < (n : ℝ) by linarith
    refine ⟨(n - 1).toNat, ?_⟩
    have hc : (((n - 1).toNat : ℤ) : ℝ) = (n : ℝ) - 1 := by
      rw [Int.toNat_of_nonneg (by lia : (0 : ℤ) ≤ n - 1)]; push_cast; ring
    rw [hxn]; push_cast at hc ⊢; linarith
  · -- `x = 0`: `ζ 0 = -1/2 ≠ 0`.
    subst hx0
    rw [Complex.ofReal_zero, riemannZeta_zero]
    norm_num
  · -- `0 < x < 1`.
    exact riemannZeta_ne_zero_of_mem_Ioo_zero_one ⟨hx0, hx1⟩
