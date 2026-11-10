/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Range-reduction lemmas for `sin` at large arguments

* `sin` modulo `π/2`: the four quadrant identities `sin_quad0..3` and the reduction lemmas
  `sin_reduce0..3`, which delegate to the generic `reduce_*_val` chain.
-/
@[expose] public section


namespace BSN
open Enclosure

-- Inside `BSN` a bare `open Real` would resolve to `BSN.Real` (home of `Real.IsNear`),
-- so open the root namespace explicitly for `π` and the trigonometric lemmas.
open _root_.Real

/-! ### Rounding the reduced argument

The reduced argument `u/v` carries the precision of the `π` constant, far beyond what the answer
needs, and the series cost grows with `v`; so the series is evaluated at a coarser `u'/v'` and the
difference is absorbed into the radius (`sin` and `cos` are 1-Lipschitz). -/

/-- Side conditions of `cos_arg_round`/`sin_arg_round`: positive denominators, `u'/v' ≤ u/v` so the
`ℕ` subtraction is the true difference, and `|u/v − u'/v'| + 1/Dp ≤ 1/D` cleared of denominators. -/
def argRoundOk (u v u' v' Dp D : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) v)
    (Nat.add (Nat.sub (nat_lit 1) v')
    (Nat.add (Nat.sub (nat_lit 1) Dp)
    (Nat.add (Nat.sub (nat_lit 1) D)
    (Nat.add (Nat.sub (u'.mul v) (u.mul v'))
             (Nat.sub (Nat.add (Nat.mul (D.mul Dp) (Nat.sub (u.mul v') (u'.mul v)))
                               (Nat.mul D (v.mul v')))
                      (Nat.mul Dp (v.mul v'))))))))
    (nat_lit 0)

/-- Unpack `argRoundOk` into the six conditions. -/
private theorem argRoundOk_parts {u v u' v' Dp D : ℕ} (hs : argRoundOk u v u' v' Dp D = true) :
    1 ≤ v ∧ 1 ≤ v' ∧ 1 ≤ Dp ∧ 1 ≤ D ∧ u' * v ≤ u * v' ∧
      D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v') := by
  simp only [argRoundOk, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.le_of_sub_eq_zero z1, Nat.le_of_sub_eq_zero z2, Nat.le_of_sub_eq_zero z3,
    Nat.le_of_sub_eq_zero z4, Nat.le_of_sub_eq_zero z5, Nat.le_of_sub_eq_zero z6⟩

/-- The rounding step: from the six unpacked conditions, the coarse argument is within
`1/D − 1/Dp` of the true one. -/
private theorem arg_round_bound {u v u' v' Dp D : ℕ}
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hDp : 1 ≤ Dp) (hD : 1 ≤ D)
    (hle : u' * v ≤ u * v')
    (hmain : D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v')) :
    |(u : ℝ) / v - (u' : ℝ) / v'| + 1 / Dp ≤ 1 / D := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hDpR : (0 : ℝ) < Dp := by exact_mod_cast hDp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hleR : ((u' : ℝ) * v) ≤ (u : ℝ) * v' := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ (u : ℝ) * v' - (u' : ℝ) * v := by linarith
  have hsub : ((u * v' - u' * v : ℕ) : ℝ) = (u : ℝ) * v' - (u' : ℝ) * v := by
    have hle' : (u' * v : ℕ) ≤ (u * v' : ℕ) := hle
    push_cast [Nat.cast_sub hle']
    ring
  have hrw : (u : ℝ) / v - (u' : ℝ) / v' = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    field_simp
  have habs : |(u : ℝ) / v - (u' : ℝ) / v'| = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    rw [hrw]
    exact abs_of_nonneg (div_nonneg hnn (by positivity))
  have hmainR : (D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v') ≤ Dp * (v * v') := by
    have hc : ((D * Dp * (u * v' - u' * v) + D * (v * v') : ℕ) : ℝ)
        ≤ ((Dp * (v * v') : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast [hsub] at hc
    linarith
  rw [← sub_nonneg, habs]
  have key : (1 : ℝ) / D - (((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') + 1 / Dp)
      = ((Dp : ℝ) * (v * v') - ((D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v')))
        / ((D : ℝ) * Dp * (v * v')) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)

/-- `cos` at a rounded argument: the series is evaluated at `u'/v'` and the difference from `u/v`
is absorbed into the radius. -/
theorem cos_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.cos ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.cos ((u : ℝ) / v) - Real.cos ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_cos_sub_cos_le _ _
  have h' : |Real.cos ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.cos ((u : ℝ) / v)) (Real.cos ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.cos ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres

/-- `sin` at a rounded argument: the series is evaluated at `u'/v'` and the difference from `u/v`
is absorbed into the radius. -/
theorem sin_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.sin ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.sin ((u : ℝ) / v) - Real.sin ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_sin_sub_sin_le _ _
  have h' : |Real.sin ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.sin ((u : ℝ) / v)) (Real.sin ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.sin ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres

/-! ### Quadrant identities (period-4 in the multiple of `π/2`) -/

/-- `k ≡ 0 (mod 4)` quadrant: `sin (r + 4q·(π/2)) = sin r`. -/
theorem sin_quad0 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ)) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi]

/-- `k ≡ 1 (mod 4)` quadrant: `sin (r + (4q+1)·(π/2)) = cos r`. -/
theorem sin_quad1 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 1) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi_div_two]

/-- `k ≡ 2 (mod 4)` quadrant: `sin (r + (4q+2)·(π/2)) = −sin r`. -/
theorem sin_quad2 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi]

/-- `k ≡ 3 (mod 4)` quadrant: `sin (r + (4q+3)·(π/2)) = −cos r`. -/
theorem sin_quad3 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 3) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi_div_two]

/-! ### The value-generic reduction chain and the `sin`/`cos` quadrant lemmas

The interval + Lipschitz reduction chain over any real `F` with an identity `F = ε·g(x − k·π/2)`;
the `sin` and `cos` quadrant wrappers instantiate it. -/

/-- Interval + Lipschitz reduction core: from `F = ε·g r`, `1`-Lipschitz `g` between `r` and the
rational centre `rc`, `|r − rc| ≤ B`, and `|g rc − q| ≤ inner`, conclude `|F − ε·q| ≤ B + inner`. -/
theorem reduce_core_val (F r rc q B inner Dinv : ℝ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hlip : |g r - g rc| ≤ |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |g rc - q| ≤ inner)
    (htot : B + inner ≤ Dinv) :
    |F - ε * q| ≤ Dinv := by
  have h1 : |F - ε * q| ≤ |g r - g rc| + |g rc - q| := by
    rw [hquad]
    calc |ε * g r - ε * q| = |ε| * |g r - q| := by rw [← mul_sub, abs_mul]
      _ = |g r - q| := by rw [hε, one_mul]
      _ ≤ |g r - g rc| + |g rc - q| := abs_sub_le _ _ _
  calc |F - ε * q| ≤ |g r - g rc| + |g rc - q| := h1
    _ ≤ B + inner := add_le_add (hlip.trans hB) hinner
    _ ≤ Dinv := htot

/-- Reduction step: combine a `π` certificate `|π − Pr| ≤ 1/E` and the in-range certificate
`|g rcv − val| ≤ 1/Dp` into `|F − ε·val| ≤ 1/D`, for `rcv = x − k·(Pr/2)`. -/
theorem reduce_step_val (F x r rcv Pr val : ℝ) (k E Dp D : ℕ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hr : r = x - (k : ℝ) * (π / 2))
    (hlip : |g r - g rcv| ≤ |r - rcv|)
    (hrc : rcv = x - (k : ℝ) * (Pr / 2))
    (hpi : |Real.pi - Pr| ≤ 1 / (E : ℝ))
    (hinner : |g rcv - val| ≤ 1 / (Dp : ℝ))
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    |F - ε * val| ≤ 1 / (D : ℝ) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at htot
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hB : |r - rcv| ≤ (k : ℝ) / (2 * E) := by
    rw [hr, hrc]
    have e : (x - (k : ℝ) * (π / 2)) - (x - (k : ℝ) * (Pr / 2)) = (k : ℝ) * (Pr / 2 - π / 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    have hhalf : |Pr / 2 - π / 2| ≤ 1 / (2 * E) := by
      have e2 : Pr / 2 - π / 2 = -(Real.pi - Pr) / 2 := by ring
      rw [e2, abs_div, abs_neg, abs_two]
      calc |Real.pi - Pr| / 2 ≤ (1 / (E : ℝ)) / 2 := by gcongr
        _ = 1 / (2 * E) := by ring
    calc (k : ℝ) * |Pr / 2 - π / 2| ≤ (k : ℝ) * (1 / (2 * E)) := by gcongr
      _ = (k : ℝ) / (2 * E) := by ring
  have htotR : (k : ℝ) / (2 * E) + 1 / (Dp : ℝ) ≤ 1 / (D : ℝ) := by
    have hc : ((k * D * Dp + 2 * E * D : ℕ) : ℝ) ≤ ((2 * E * Dp : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at hc
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hc, hEr, hDpr, hDr]
  exact reduce_core_val F r rcv val ((k : ℝ) / (2 * E)) (1 / Dp) (1 / D) ε g hε hquad
    hlip hB hinner htotR

/-- Master quadrant lemma over any real `F`: turn an in-range enclosure of `g rcv` at
`rcv = x − k·((Pc/PQ)/2)` into an enclosure of `F`. -/
theorem reduce_quad_val (F x rcv : ℝ) (g : ℝ → ℝ) (ε : ℝ) (Pc PQ : ℕ) (ineg oneg : Bool)
    (icn Qd k E Dp D : ℕ)
    (hε : |ε| = 1)
    (hquad : F = ε * g (x - (k : ℝ) * (π / 2)))
    (hlip : ∀ a b, |g a - g b| ≤ |a - b|)
    (hsign : sfrac oneg icn Qd = ε * sfrac ineg icn Qd)
    (hrc : rcv = x - (k : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (g rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear F oneg icn Qd 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpi
  rw [← sfrac_false_div Pc PQ] at hpi
  rw [Real.IsNear, Nat.cast_one] at hinner
  rw [Real.IsNear, Nat.cast_one, hsign]
  exact reduce_step_val F x (x - (k : ℝ) * (π / 2)) rcv (sfrac false Pc PQ)
    (sfrac ineg icn Qd) k E Dp D ε g hε hquad rfl (hlip _ _) hrc hpi hinner hE hDp hD htot

/-- `k ≡ 0 (mod 4)` quadrant for `cos`: `cos (r + 4q·(π/2)) = cos r`. -/
theorem cos_quad0 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ)) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi]

/-- `k ≡ 1 (mod 4)` quadrant for `cos`: `cos (r + (4q+1)·(π/2)) = −sin r`. -/
theorem cos_quad1 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 1) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi_div_two]

/-- `k ≡ 2 (mod 4)` quadrant for `cos`: `cos (r + (4q+2)·(π/2)) = −cos r`. -/
theorem cos_quad2 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi]

/-- `k ≡ 3 (mod 4)` quadrant for `cos`: `cos (r + (4q+3)·(π/2)) = sin r`. -/
theorem cos_quad3 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 3) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi, cos_add_pi_div_two, neg_neg]

/-! ### The `sin` and `cos` reduction lemmas -/

/-- Quadrant `k ≡ 0`: in-range `g = sin`, sign `ε = +1`. -/
theorem sin_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← sin_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 1`: in-range `g = cos`, sign `ε = +1`. -/
theorem sin_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq + 1) E Dp D abs_one
    (by rw [one_mul, ← sin_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 2`: in-range `g = sin`, sign `ε = −1` (the in-range centre's sign flips). -/
theorem sin_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 3`: in-range `g = cos`, sign `ε = −1` (the in-range centre's sign flips). -/
theorem sin_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 3) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 0` for `cos`: in-range `g = cos`, sign `ε = +1`. -/
theorem cos_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← cos_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 1` for `cos`: in-range `g = sin`, sign `ε = −1`. -/
theorem cos_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 1) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 2` for `cos`: in-range `g = cos`, sign `ε = −1`. -/
theorem cos_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/-- Quadrant `k ≡ 3` for `cos`: in-range `g = sin`, sign `ε = +1`. -/
theorem cos_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq + 3) E Dp D
    abs_one
    (by rw [one_mul, ← cos_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/-- The rational centre identity: with `v = 2·b·PQ` and the `ℕ` link `2·a·PQ = u + k·(b·Pc)`, the
rational `u/v` equals `a/b − k·(Pr/2)` for `Pr = sfrac false Pc PQ`. -/
theorem sin_reduce_arg_pos_rat (a b Pc PQ k u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add (k.mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - (k : ℝ) * (sfrac false Pc PQ / 2) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink hv
  subst hv
  rw [sfrac_false_div]
  have hQr : (0 : ℝ) < PQ := pos_real_of_ble hQ
  have hbr : (0 : ℝ) < b := pos_real_of_ble hb
  have hlinkR : (2 * a * PQ : ℝ) = (u + k * (b * Pc) : ℝ) := by exact_mod_cast hlink
  push_cast
  field_simp
  ring_nf
  linarith [hlinkR]

/-! ### Centre identities in each quadrant's own multiplier shape

`sin_reduce_arg_pos_rat` with the multiplier stated as `4·qq + j`, the shape each quadrant lemma
expects, so the kernel need not reconcile it with a single `k` at every reduction. -/

theorem sin_reduce_arg_pos_rat_q0 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.mul 4 qq).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q1 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 1).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 1) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q2 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 2).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 2) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q3 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 3).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 3) u v hlink hv hQ hb

end BSN
