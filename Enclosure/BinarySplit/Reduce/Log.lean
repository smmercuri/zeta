/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Range-reduction lemmas for `log` by powers of two

`log(a/b) = log((a/b)/2ᵏ) + k·log 2` (`log_reduce_eq`), assembled into an `IsNear` enclosure by
`log_rat_reduce_isNear`, with helpers `log_nat_of_cert`, `log_two_eq`, `logfrac_isNear`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-! ### `log` range reduction by powers of two -/

/-- Recast the `log` enclosure's argument `↑S/↑Dd` as `Real.log ↑n` when `S = n` and `Dd = 1`. -/
theorem log_nat_of_cert (S Dd n : ℕ) (neg : Bool) (cn cd rn rd : ℕ)
    (hs : Nat.beq S n) (hd : Nat.beq Dd 1)
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) neg cn cd rn rd) :
    Real.IsNear (Real.log ((n : ℕ) : ℝ)) neg cn cd rn rd := by
  have hs' : S = n := Nat.eq_of_beq_eq_true hs
  have hd' : Dd = 1 := Nat.eq_of_beq_eq_true hd
  rw [hs', hd'] at h
  rwa [Nat.cast_one, div_one] at h

/-- Log range reduction: `log(N/M) = log(N/(M·2ᵏ)) + k·log 2`. -/
theorem log_reduce_eq (N M k : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Real.log ((N : ℝ) / M) = Real.log ((N : ℝ) / (M * 2 ^ k)) + (k : ℝ) * Real.log 2 := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have e : (N : ℝ) / (M * 2 ^ k) = ((N : ℝ) / M) / 2 ^ k := by rw [div_div]
  have key : Real.log ((N : ℝ) / (M * 2 ^ k)) = Real.log ((N : ℝ) / M) - (k : ℝ) * Real.log 2 := by
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [key]; ring

/-- Range reduction for `log(a/b)`: from a reduced certificate
`|log((2a)/(b·2^{k+1})) − pr/Qr| ≤ 1/D` and `|log 2 − p2/Q2| ≤ 1/E`, conclude `IsNear (log(a/b))`
with centre `pr/Qr + k·(p2/Q2)` and radius `1/D + k/E`. -/
theorem log_rat_reduce_isNear (a b k S Dd pr Qr p2 Q2 D E : ℕ) (ha : Nat.ble 1 a)
    (hb : Nat.ble 1 b)
    (hS : S.beq (Nat.mul 2 a)) (hDd : Dd.beq (Nat.mul b (Nat.pow 2 (Nat.succ k))))
    (hr : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false pr Qr 1 D)
    (h2 : Real.IsNear (Real.log 2) false p2 Q2 1 E)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hQr : Nat.ble 1 Qr) (hQ2 : Nat.ble 1 Q2) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false ((pr.mul Q2).add ((k.mul p2).mul Qr)) (Qr.mul Q2)
      (E.add (k.mul D)) (D.mul E) := by
  obtain rfl := Nat.eq_of_beq_eq_true hS
  obtain rfl := Nat.eq_of_beq_eq_true hDd
  simp only [Nat.mul_eq, Nat.add_eq, Nat.pow_eq] at hr ⊢
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hr h2
  have hDR : (0:ℝ) < D := pos_real_of_ble hD
  have hER : (0:ℝ) < E := pos_real_of_ble hE
  have hQrR : (0:ℝ) < Qr := pos_real_of_ble hQr
  have hQ2R : (0:ℝ) < Q2 := pos_real_of_ble hQ2
  have harg : ((↑(2 * a) : ℝ) / ((b * 2 ^ (k + 1) : ℕ) : ℝ)) = (↑a : ℝ) / ((b : ℝ) * 2 ^ k) := by
    push_cast; ring
  rw [harg] at hr
  have hlogn : Real.log ((↑a : ℝ) / b)
      = Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2 :=
    log_reduce_eq a b k (pos_of_ble ha) (pos_of_ble hb)
  have hcentre : ((pr * Q2 + k * p2 * Qr : ℕ) : ℝ) / ((Qr * Q2 : ℕ) : ℝ)
              = (pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2) := by
    push_cast; field_simp [hQrR.ne', hQ2R.ne']
  have hrad : ((E + k * D : ℕ) : ℝ) / ((D * E : ℕ) : ℝ) = 1 / ↑D + ↑k * (1 / ↑E) := by
    push_cast; field_simp [hDR.ne', hER.ne']
  rw [Real.IsNear, sfrac_false_div, hlogn, hcentre, hrad]
  calc |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) + ↑k * Real.log 2
          - ((pr : ℝ) / Qr + ↑k * ((p2 : ℝ) / Q2))|
      = |(Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr)
          + ↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := by ring_nf
    _ ≤ |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + |↑k * (Real.log 2 - (p2 : ℝ) / Q2)| := abs_add_le _ _
    _ = |Real.log ((↑a : ℝ) / ((b : ℝ) * 2 ^ k)) - (pr : ℝ) / Qr|
          + ↑k * |Real.log 2 - (p2 : ℝ) / Q2| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ 1 / ↑D + ↑k * (1 / ↑E) := by gcongr

/-- Recast the `u=1, v=3` log enclosure (`log(4/2)`, literal numerator and denominator) as a
`log 2` enclosure. -/
theorem log_two_eq (p2 Q2 E : ℕ)
    (h : Real.IsNear (Real.log (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ))) false p2 Q2 1 E) :
    Real.IsNear (Real.log 2) false p2 Q2 1 E := by
  have e : (((4 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 2 := by norm_num
  rwa [e] at h

/-- Rewrite a `log(S/Dd)` certificate as `log(a/b)` when `S·g = 2a` and `Dd·g = 2b` for a positive
weight `g` (so `S/Dd = a/b`). -/
theorem logfrac_isNear (S Dd g a b p Q D : ℕ) (hg : Nat.ble 1 g)
    (hs : Nat.beq (S.mul g) (Nat.mul 2 a))
    (hd : Nat.beq (Dd.mul g) (Nat.mul 2 b))
    (h : Real.IsNear (Real.log ((S : ℝ) / (Dd : ℝ))) false p Q 1 D) :
    Real.IsNear (Real.log ((a : ℝ) / b)) false p Q 1 D := by
  have hs' : S * g = 2 * a := Nat.eq_of_beq_eq_true hs
  have hd' : Dd * g = 2 * b := Nat.eq_of_beq_eq_true hd
  have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_ble hg).ne'
  have h1 : (S : ℝ) * g = 2 * a := by exact_mod_cast hs'
  have h2 : (Dd : ℝ) * g = 2 * b := by exact_mod_cast hd'
  have e : ((S : ℝ) / (Dd : ℝ)) = (a : ℝ) / b := by
    calc (S : ℝ) / (Dd : ℝ)
        = (S : ℝ) * g / ((Dd : ℝ) * g) := (mul_div_mul_right _ _ hgR).symm
      _ = 2 * (a : ℝ) / (2 * (b : ℝ)) := by rw [h1, h2]
      _ = (a : ℝ) / b := mul_div_mul_left _ _ two_ne_zero
  rwa [e] at h


end BSN
