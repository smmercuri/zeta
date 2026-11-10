/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Log

/-!
# High-precision `log 2` via a Machin-like decomposition

`log 2 = 7·log(16/15) + 5·log(25/24) + 3·log(81/80)`, each factor a `log((k+1)/k)` certified
by `log_dyadic_bound`, combined with weights `7, 5, 3`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Machin combiner for `log 2`: from enclosures (denominator `Q`, precision `1/D`) of the three
factors `log(32/30)`, `log(50/48)`, `log(162/160)`, conclude `log 2` at precision `1/E` when
`15·E ≤ D`, centre `P = 7p₁ + 5p₂ + 3p₃`. -/
theorem log2_combine (p₁ p₂ p₃ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 15 E).ble D)
    (hP : P.beq (((Nat.mul 7 p₁).add (Nat.mul 5 p₂)).add (Nat.mul 3 p₃)))
    (h₁ : Real.IsNear (Real.log (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ))) false p₁ Q 1 D)
    (h₂ : Real.IsNear (Real.log (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ))) false p₂ Q 1 D)
    (h₃ : Real.IsNear (Real.log (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ))) false p₃ Q 1 D) :
    Real.IsNear (Real.log 2) false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ h₃ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  subst hP
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have e₁ : (((32 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = 16 / 15 := by norm_num
  have e₂ : (((50 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = 25 / 24 := by norm_num
  have e₃ : (((162 : ℕ) : ℝ) / ((160 : ℕ) : ℝ)) = 81 / 80 := by norm_num
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  have hdecomp : Real.log 2 = 7 * Real.log (16 / 15) + 5 * Real.log (25 / 24)
      + 3 * Real.log (81 / 80) := by
    have h2 : (2 : ℝ) = (16 / 15) ^ 7 * ((25 / 24) ^ 5 * (81 / 80) ^ 3) := by norm_num
    rw [h2, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have key : Real.log 2 - ((7 * p₁ + 5 * p₂ + 3 * p₃ : ℕ) : ℝ) / Q
      = 7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
        + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q) := by
    rw [hdecomp]; push_cast; ring
  rw [key]
  calc |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q) + 5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)
          + 3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)|
      ≤ |7 * (Real.log (16 / 15) - (p₁ : ℝ) / Q)|
          + |5 * (Real.log (25 / 24) - (p₂ : ℝ) / Q)|
          + |3 * (Real.log (81 / 80) - (p₃ : ℝ) / Q)| := abs_add_three _ _ _
    _ = 7 * |Real.log (16 / 15) - (p₁ : ℝ) / Q| + 5 * |Real.log (25 / 24) - (p₂ : ℝ) / Q|
          + 3 * |Real.log (81 / 80) - (p₃ : ℝ) / Q| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ 7 * (1 / D) + 5 * (1 / D) + 3 * (1 / D) := by gcongr
    _ = 15 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE

end BSN
