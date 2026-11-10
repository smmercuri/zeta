/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure
public import Enclosure.BinarySplit.Taylor

/-!
# The cosine Taylor sum as a single fraction with literal coefficients

`cos_poly_sum` rewrites the degree-18 partial sum of `cos (u/v)` as `(P - N) / (v^18 · 18!)`, with
`P` and `N` the even- and odd-indexed terms, each a sum of five products of a literal coefficient
`18!/(2i)!` with `u^{2i} v^{18-2i}`.

Unlike the binary-split form, which carries the split's own denominators and a `binarySplit`
certificate chain, this is a fixed polynomial in `u` and `v` with numeral coefficients.
-/

@[expose] public section

namespace BSN

open Enclosure Finset

/-- The degree-18 Taylor partial sum of `cos (u/v)` as one fraction over `v^18 · 18!`, term `i`
becoming `(-1)^i · (18!/(2i)!) · u^{2i} v^{18-2i}`. -/
theorem cos_poly_sum (u v : ℕ) (hv : v ≠ 0) :
    ∑ i ∈ range 10, (-1 : ℚ) ^ i * ((u : ℚ) / v) ^ (2 * i) / (2 * i).factorial
      = ((6402373705728000 * (v : ℚ) ^ 18
            + 266765571072000 * (u : ℚ) ^ 4 * (v : ℚ) ^ 14
            + 158789030400 * (u : ℚ) ^ 8 * (v : ℚ) ^ 10
            + 13366080 * (u : ℚ) ^ 12 * (v : ℚ) ^ 6
            + 306 * (u : ℚ) ^ 16 * (v : ℚ) ^ 2)
          - (3201186852864000 * (u : ℚ) ^ 2 * (v : ℚ) ^ 16
            + 8892185702400 * (u : ℚ) ^ 6 * (v : ℚ) ^ 12
            + 1764322560 * (u : ℚ) ^ 10 * (v : ℚ) ^ 8
            + 73440 * (u : ℚ) ^ 14 * (v : ℚ) ^ 4
            + (u : ℚ) ^ 18))
        / ((v : ℚ) ^ 18 * 6402373705728000) := by
  have hvq : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- The eight numeral conditions of `cos_poly_bound` as a single `Bool`, with the two polynomial
sums bound once by `let`. -/
def cosPolyOk (u v Q D cn : ℕ) : Bool :=
  let N : ℕ := Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul 3201186852864000 (Nat.mul (Nat.pow u 2) (Nat.pow v 16)))
    (Nat.mul 8892185702400 (Nat.mul (Nat.pow u 6) (Nat.pow v 12))))
    (Nat.mul 1764322560 (Nat.mul (Nat.pow u 10) (Nat.pow v 8))))
    (Nat.mul 73440 (Nat.mul (Nat.pow u 14) (Nat.pow v 4))))
    (Nat.pow u 18)
  let P : ℕ := Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul 6402373705728000 (Nat.pow v 18))
    (Nat.mul 266765571072000 (Nat.mul (Nat.pow u 4) (Nat.pow v 14))))
    (Nat.mul 158789030400 (Nat.mul (Nat.pow u 8) (Nat.pow v 10))))
    (Nat.mul 13366080 (Nat.mul (Nat.pow u 12) (Nat.pow v 6))))
    (Nat.mul 306 (Nat.mul (Nat.pow u 16) (Nat.pow v 2)))
  Nat.ble 1 v && Nat.ble 1 D && Nat.blt u (Nat.mul 21 v) &&
    Nat.ble (Nat.mul 2 (Nat.pow u 2)) (Nat.mul 441 (Nat.pow v 2)) &&
    Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow u 20)) (Nat.mul 2 D))
      (Nat.mul (Nat.pow v 20) 2432902008176640000) &&
    Nat.ble (Nat.add (Nat.mul cn (Nat.mul (Nat.pow v 18) 6402373705728000)) (Nat.mul N Q))
      (Nat.mul P Q) &&
    Nat.blt (Nat.mul P Q)
      (Nat.add (Nat.mul (Nat.succ cn) (Nat.mul (Nat.pow v 18) 6402373705728000)) (Nat.mul N Q)) &&
    Nat.ble (Nat.mul 2 D) Q

/-- `cos (u/v)` to `1/D`, from the degree-18 Taylor polynomial with literal coefficients, for a
nonnegative centre. The conditions are plain `Nat` comparisons: `hu`/`hu2` bound the argument for
the remainder estimate, `htail` bounds the remainder by `1/(2D)` through `20!`, and `hr1`/`hr2`
make `cn/Q` the floor of the polynomial value. -/
theorem cos_poly_bound (u v Q D cn : ℕ)
    (hv : Nat.ble 1 v = true) (hD : Nat.ble 1 D = true)
    (hu : Nat.blt u (Nat.mul 21 v) = true)
    (hu2 : Nat.ble (Nat.mul 2 (Nat.pow u 2)) (Nat.mul 441 (Nat.pow v 2)) = true)
    (htail : Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow u 20)) (Nat.mul 2 D))
      (Nat.mul (Nat.pow v 20) 2432902008176640000) = true)
    (hr1 : Nat.ble
      (Nat.add (Nat.mul cn (Nat.mul (Nat.pow v 18) 6402373705728000))
        (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
          (Nat.mul 3201186852864000 (Nat.mul (Nat.pow u 2) (Nat.pow v 16)))
          (Nat.mul 8892185702400 (Nat.mul (Nat.pow u 6) (Nat.pow v 12))))
          (Nat.mul 1764322560 (Nat.mul (Nat.pow u 10) (Nat.pow v 8))))
          (Nat.mul 73440 (Nat.mul (Nat.pow u 14) (Nat.pow v 4))))
          (Nat.pow u 18)) Q))
      (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
        (Nat.mul 6402373705728000 (Nat.pow v 18))
        (Nat.mul 266765571072000 (Nat.mul (Nat.pow u 4) (Nat.pow v 14))))
        (Nat.mul 158789030400 (Nat.mul (Nat.pow u 8) (Nat.pow v 10))))
        (Nat.mul 13366080 (Nat.mul (Nat.pow u 12) (Nat.pow v 6))))
        (Nat.mul 306 (Nat.mul (Nat.pow u 16) (Nat.pow v 2)))) Q) = true)
    (hr2 : Nat.blt
      (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
        (Nat.mul 6402373705728000 (Nat.pow v 18))
        (Nat.mul 266765571072000 (Nat.mul (Nat.pow u 4) (Nat.pow v 14))))
        (Nat.mul 158789030400 (Nat.mul (Nat.pow u 8) (Nat.pow v 10))))
        (Nat.mul 13366080 (Nat.mul (Nat.pow u 12) (Nat.pow v 6))))
        (Nat.mul 306 (Nat.mul (Nat.pow u 16) (Nat.pow v 2)))) Q)
      (Nat.add (Nat.mul (Nat.succ cn) (Nat.mul (Nat.pow v 18) 6402373705728000))
        (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
          (Nat.mul 3201186852864000 (Nat.mul (Nat.pow u 2) (Nat.pow v 16)))
          (Nat.mul 8892185702400 (Nat.mul (Nat.pow u 6) (Nat.pow v 12))))
          (Nat.mul 1764322560 (Nat.mul (Nat.pow u 10) (Nat.pow v 8))))
          (Nat.mul 73440 (Nat.mul (Nat.pow u 14) (Nat.pow v 4))))
          (Nat.pow u 18)) Q)) = true)
    (hQ : Nat.ble (Nat.mul 2 D) Q = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one]
    at hu hu2 hv hD htail hr1 hr2 hQ
  have hvN : 0 < v := hv
  have hDN : 0 < D := hD
  have hvne : v ≠ 0 := hvN.ne'
  have hvr : (0 : ℝ) < v := by exact_mod_cast hvN
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDN
  have hQ0 : 0 < Q := by lia
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  -- the polynomial value, as the two sums the statement's conditions use
  set P : ℕ := 6402373705728000 * v ^ 18 + 266765571072000 * (u ^ 4 * v ^ 14)
    + 158789030400 * (u ^ 8 * v ^ 10) + 13366080 * (u ^ 12 * v ^ 6) + 306 * (u ^ 16 * v ^ 2)
    with hP
  set N : ℕ := 3201186852864000 * (u ^ 2 * v ^ 16) + 8892185702400 * (u ^ 6 * v ^ 12)
    + 1764322560 * (u ^ 10 * v ^ 8) + 73440 * (u ^ 14 * v ^ 4) + u ^ 18 with hN
  set Den : ℕ := v ^ 18 * 6402373705728000 with hDen
  have hDenr : (0 : ℝ) < Den := by rw [hDen]; positivity
  -- the value is the degree-18 partial sum, by `cos_poly_sum`
  have hvalR : ((P : ℝ) / Den - (N : ℝ) / Den)
      = ∑ i ∈ range 10, (-1 : ℝ) ^ i * ((u : ℝ) / v) ^ (2 * i) / (2 * i).factorial := by
    have hq := congrArg (fun r : ℚ ↦ (r : ℝ)) (cos_poly_sum u v hvne)
    push_cast at hq
    rw [hP, hN, hDen]
    push_cast
    rw [div_sub_div_same] at *
    convert hq.symm using 2
    ring
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((10 : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hvr]; push_cast; exact_mod_cast hu
  have hcos := cos_sub_sum_le ((u : ℝ) / v) 10 hxnn hxlt
  rw [← hvalR] at hcos
  have hcos' : |Real.cos ((u : ℝ) / v) - ((P : ℝ) / Den - (N : ℝ) / Den)| ≤ 1 / (2 * D) := by
    refine hcos.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * 10) / (2 * 10).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * 10) * 2 * (2 * D) = 2 * (u : ℝ) ^ 20 * (2 * D) := by
        ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ 20 * (2 * D) ≤ (v : ℝ) ^ 20 * 2432902008176640000 := by
        exact_mod_cast htail
      refine htR.trans (le_of_eq ?_)
      norm_num [Nat.factorial]
    refine le_trans ?_ hA2
    gcongr
    exact geo_factor_le _ _ (by positivity) (by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      push_cast
      exact_mod_cast hu2)
  have hr1' : (cn : ℝ) * Den + (N : ℝ) * Q ≤ (P : ℝ) * Q := by exact_mod_cast hr1
  have hr2' : (P : ℝ) * Q < ((cn : ℝ) + 1) * Den + (N : ℝ) * Q := by exact_mod_cast hr2
  rw [Real.IsNear, Nat.cast_one, sfrac_false_div]
  exact grid_round _ ((P : ℝ) - N) Den cn Q D (by rwa [div_sub_div_same] at hcos') (by linarith)
    (by linarith) hDenr hDr hQr hQ

/-- `cos_poly_bound` from the packed condition `cosPolyOk`, checked by one reflection proof. -/
theorem cos_poly_bound_packed (u v Q D cn : ℕ) (h : cosPolyOk u v Q D cn = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) false cn Q 1 D := by
  simp only [cosPolyOk, Bool.and_eq_true] at h
  exact cos_poly_bound u v Q D cn h.1.1.1.1.1.1.1 h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2
    h.1.1.1.2 h.1.1.2 h.1.2 h.2

end BSN
