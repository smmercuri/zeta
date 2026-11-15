/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure
public import Enclosure.BinarySplit.Taylor

/-!
# The sine Taylor sum as a single fraction with literal coefficients

The sine counterpart of `CosPoly`: `sin_poly_sum` rewrites the ten-term partial sum of `sin (u/v)`
as `(P - N) / (v^19 · 19!)`, and `sin_poly_bound` turns that into an enclosure from plain `Nat`
conditions.
-/

@[expose] public section

namespace BSN

open Enclosure Finset

/-- The ten-term Taylor partial sum of `sin (u/v)` as one fraction over `v^19 · 19!`, term `k`
becoming `(-1)^k · (19!/(2k+1)!) · u^{2k+1} v^{18-2k}`. -/
theorem sin_poly_sum (u v : ℕ) (hv : v ≠ 0) :
    ∑ k ∈ range 10, (-1 : ℚ) ^ k * ((u : ℚ) / v) ^ (2 * k + 1) / (2 * k + 1).factorial
      = ((121645100408832000 * (u : ℚ) * (v : ℚ) ^ 18
            + 1013709170073600 * (u : ℚ) ^ 5 * (v : ℚ) ^ 14
            + 335221286400 * (u : ℚ) ^ 9 * (v : ℚ) ^ 10
            + 19535040 * (u : ℚ) ^ 13 * (v : ℚ) ^ 6
            + 342 * (u : ℚ) ^ 17 * (v : ℚ) ^ 2)
          - (20274183401472000 * (u : ℚ) ^ 3 * (v : ℚ) ^ 16
            + 24135932620800 * (u : ℚ) ^ 7 * (v : ℚ) ^ 12
            + 3047466240 * (u : ℚ) ^ 11 * (v : ℚ) ^ 8
            + 93024 * (u : ℚ) ^ 15 * (v : ℚ) ^ 4
            + (u : ℚ) ^ 19))
        / ((v : ℚ) ^ 19 * 121645100408832000) := by
  have hvq : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- The eight numeral conditions of `sin_poly_bound` as a single `Bool`, with the two polynomial
sums bound by `let`; the `sin` twin of `cosPolyOk`. -/
def sinPolyOk (u v Q D cn : ℕ) : Bool :=
  let N : ℕ := Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul 20274183401472000 (Nat.mul (Nat.pow u 3) (Nat.pow v 16)))
    (Nat.mul 24135932620800 (Nat.mul (Nat.pow u 7) (Nat.pow v 12))))
    (Nat.mul 3047466240 (Nat.mul (Nat.pow u 11) (Nat.pow v 8))))
    (Nat.mul 93024 (Nat.mul (Nat.pow u 15) (Nat.pow v 4))))
    (Nat.pow u 19)
  let P : ℕ := Nat.add (Nat.add (Nat.add (Nat.add
    (Nat.mul 121645100408832000 (Nat.mul u (Nat.pow v 18)))
    (Nat.mul 1013709170073600 (Nat.mul (Nat.pow u 5) (Nat.pow v 14))))
    (Nat.mul 335221286400 (Nat.mul (Nat.pow u 9) (Nat.pow v 10))))
    (Nat.mul 19535040 (Nat.mul (Nat.pow u 13) (Nat.pow v 6))))
    (Nat.mul 342 (Nat.mul (Nat.pow u 17) (Nat.pow v 2)))
  Nat.ble 1 v && Nat.ble 1 D && Nat.blt u (Nat.mul 22 v) &&
    Nat.ble (Nat.mul 2 (Nat.pow u 2)) (Nat.mul 484 (Nat.pow v 2)) &&
    Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow u 21)) (Nat.mul 2 D))
      (Nat.mul (Nat.pow v 21) 51090942171709440000) &&
    Nat.ble (Nat.add (Nat.mul cn (Nat.mul (Nat.pow v 19) 121645100408832000)) (Nat.mul N Q))
      (Nat.mul P Q) &&
    Nat.blt (Nat.mul P Q)
      (Nat.add (Nat.mul (Nat.succ cn) (Nat.mul (Nat.pow v 19) 121645100408832000))
        (Nat.mul N Q)) &&
    Nat.ble (Nat.mul 2 D) Q

/-- `sin (u/v)` to `1/D`, from the ten-term Taylor polynomial with literal coefficients. The
conditions mirror `cos_poly_bound`, with `22` as the argument radius and `21!` in the tail. -/
theorem sin_poly_bound (u v Q D cn : ℕ)
    (hv : Nat.ble 1 v = true) (hD : Nat.ble 1 D = true)
    (hu : Nat.blt u (Nat.mul 22 v) = true)
    (hu2 : Nat.ble (Nat.mul 2 (Nat.pow u 2)) (Nat.mul 484 (Nat.pow v 2)) = true)
    (htail : Nat.ble (Nat.mul (Nat.mul 2 (Nat.pow u 21)) (Nat.mul 2 D))
      (Nat.mul (Nat.pow v 21) 51090942171709440000) = true)
    (hr1 : Nat.ble
      (Nat.add (Nat.mul cn (Nat.mul (Nat.pow v 19) 121645100408832000))
        (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
          (Nat.mul 20274183401472000 (Nat.mul (Nat.pow u 3) (Nat.pow v 16)))
          (Nat.mul 24135932620800 (Nat.mul (Nat.pow u 7) (Nat.pow v 12))))
          (Nat.mul 3047466240 (Nat.mul (Nat.pow u 11) (Nat.pow v 8))))
          (Nat.mul 93024 (Nat.mul (Nat.pow u 15) (Nat.pow v 4))))
          (Nat.pow u 19)) Q))
      (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
        (Nat.mul 121645100408832000 (Nat.mul u (Nat.pow v 18)))
        (Nat.mul 1013709170073600 (Nat.mul (Nat.pow u 5) (Nat.pow v 14))))
        (Nat.mul 335221286400 (Nat.mul (Nat.pow u 9) (Nat.pow v 10))))
        (Nat.mul 19535040 (Nat.mul (Nat.pow u 13) (Nat.pow v 6))))
        (Nat.mul 342 (Nat.mul (Nat.pow u 17) (Nat.pow v 2)))) Q) = true)
    (hr2 : Nat.blt
      (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
        (Nat.mul 121645100408832000 (Nat.mul u (Nat.pow v 18)))
        (Nat.mul 1013709170073600 (Nat.mul (Nat.pow u 5) (Nat.pow v 14))))
        (Nat.mul 335221286400 (Nat.mul (Nat.pow u 9) (Nat.pow v 10))))
        (Nat.mul 19535040 (Nat.mul (Nat.pow u 13) (Nat.pow v 6))))
        (Nat.mul 342 (Nat.mul (Nat.pow u 17) (Nat.pow v 2)))) Q)
      (Nat.add (Nat.mul (Nat.succ cn) (Nat.mul (Nat.pow v 19) 121645100408832000))
        (Nat.mul (Nat.add (Nat.add (Nat.add (Nat.add
          (Nat.mul 20274183401472000 (Nat.mul (Nat.pow u 3) (Nat.pow v 16)))
          (Nat.mul 24135932620800 (Nat.mul (Nat.pow u 7) (Nat.pow v 12))))
          (Nat.mul 3047466240 (Nat.mul (Nat.pow u 11) (Nat.pow v 8))))
          (Nat.mul 93024 (Nat.mul (Nat.pow u 15) (Nat.pow v 4))))
          (Nat.pow u 19)) Q)) = true)
    (hQ : Nat.ble (Nat.mul 2 D) Q = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one]
    at hu hu2 hv hD htail hr1 hr2 hQ
  have hvN : 0 < v := hv
  have hDN : 0 < D := hD
  have hvne : v ≠ 0 := hvN.ne'
  have hvr : (0 : ℝ) < v := by exact_mod_cast hvN
  have hDr : (0 : ℝ) < D := by exact_mod_cast hDN
  have hQ0 : 0 < Q := by lia
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set P : ℕ := 121645100408832000 * (u * v ^ 18) + 1013709170073600 * (u ^ 5 * v ^ 14)
    + 335221286400 * (u ^ 9 * v ^ 10) + 19535040 * (u ^ 13 * v ^ 6) + 342 * (u ^ 17 * v ^ 2)
    with hP
  set N : ℕ := 20274183401472000 * (u ^ 3 * v ^ 16) + 24135932620800 * (u ^ 7 * v ^ 12)
    + 3047466240 * (u ^ 11 * v ^ 8) + 93024 * (u ^ 15 * v ^ 4) + u ^ 19 with hN
  set Den : ℕ := v ^ 19 * 121645100408832000 with hDen
  have hDenr : (0 : ℝ) < Den := by rw [hDen]; positivity
  have hvalR : ((P : ℝ) / Den - (N : ℝ) / Den)
      = ∑ k ∈ range 10, (-1 : ℝ) ^ k * ((u : ℝ) / v) ^ (2 * k + 1) / (2 * k + 1).factorial := by
    have hq := congrArg (fun r : ℚ ↦ (r : ℝ)) (sin_poly_sum u v hvne)
    push_cast at hq
    rw [hP, hN, hDen]
    push_cast
    rw [div_sub_div_same] at *
    convert hq.symm using 2
    ring
  have hxnn : (0 : ℝ) ≤ (u : ℝ) / v := by positivity
  have hxlt : (u : ℝ) / v < 2 * ((10 : ℕ) : ℝ) + 2 := by
    rw [div_lt_iff₀ hvr]; push_cast; exact_mod_cast hu
  have hsin := sin_sub_sum_le ((u : ℝ) / v) 10 hxnn hxlt
  rw [← hvalR] at hsin
  have hsin' : |Real.sin ((u : ℝ) / v) - ((P : ℝ) / Den - (N : ℝ) / Den)| ≤ 1 / (2 * D) := by
    refine hsin.trans ?_
    have hA2 : ((u : ℝ) / v) ^ (2 * 10 + 1) / (2 * 10 + 1).factorial * 2 ≤ 1 / (2 * D) := by
      rw [div_pow, div_div, div_mul_eq_mul_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have e : (u : ℝ) ^ (2 * 10 + 1) * 2 * (2 * D) = 2 * (u : ℝ) ^ 21 * (2 * D) := by ring
      rw [e]
      have htR : 2 * (u : ℝ) ^ 21 * (2 * D) ≤ (v : ℝ) ^ 21 * 51090942171709440000 := by
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
  exact grid_round _ ((P : ℝ) - N) Den cn Q D (by rwa [div_sub_div_same] at hsin') (by linarith)
    (by linarith) hDenr hDr hQr hQ

/-- `sin_poly_bound` behind the packed condition `sinPolyOk`, so the emitted certificate carries
one reflection proof for all eight conditions. -/
theorem sin_poly_bound_packed (u v Q D cn : ℕ) (h : sinPolyOk u v Q D cn = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) false cn Q 1 D := by
  simp only [sinPolyOk, Bool.and_eq_true] at h
  exact sin_poly_bound u v Q D cn h.1.1.1.1.1.1.1 h.1.1.1.1.1.1.2 h.1.1.1.1.1.2 h.1.1.1.1.2
    h.1.1.1.2 h.1.1.2 h.1.2 h.2

end BSN
