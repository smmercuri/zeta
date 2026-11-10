/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Functions.Arctan

/-!
# Certified dyadic bound for `π` via Machin's formula

From Machin's `π = 16·arctan(1/5) − 4·arctan(1/239)`: bound each arctan factor to precision `1/D`
(`arctan_dyadic_bound`) and combine with weights `16, −4` to get `π` to precision `1/E`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Machin combiner for `π`: from enclosures (denominator `Q`, precision `1/D`) of `arctan(1/5)`
and `arctan(1/239)`, conclude `π` at precision `1/E` when `20·E ≤ D`, centre `P = 16·c₁ − 4·c₂`. -/
theorem pi_combine (c₁ c₂ Q D E P : ℕ)
    (hD : Nat.ble 1 D) (hE : Nat.ble 1 E) (hDE : (Nat.mul 20 E).ble D)
    (hP : (P.add (Nat.mul 4 c₂)).beq (Nat.mul 16 c₁))
    (h₁ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))) false c₁ Q 1 D)
    (h₂ : Real.IsNear (Real.arctan (((1 : ℕ) : ℝ) / ((239 : ℕ) : ℝ))) false c₂ Q 1 D) :
    Real.IsNear Real.pi false P Q 1 E := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at h₁ h₂ ⊢
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hDE hP
  -- `Nat.cast_one` above also rewrote the `↑1` numerators inside the arctan arguments
  have harg5 : ((1 : ℝ) / ((5 : ℕ) : ℝ)) = 5⁻¹ := by norm_num
  have harg239 : ((1 : ℝ) / ((239 : ℕ) : ℝ)) = 239⁻¹ := by norm_num
  rw [harg5] at h₁
  rw [harg239] at h₂
  have hmachin : Real.pi = 16 * Real.arctan 5⁻¹ - 4 * Real.arctan 239⁻¹ := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    linarith
  have hPr : (P : ℝ) = 16 * c₁ - 4 * c₂ := by
    have h : (P : ℝ) + 4 * c₂ = 16 * c₁ := by exact_mod_cast hP
    linarith
  have key : Real.pi - (P : ℝ) / Q
      = 16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
        - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q) := by
    rw [hmachin, hPr]; ring
  rw [key]
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  calc |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)
          - 4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)|
      ≤ |16 * (Real.arctan 5⁻¹ - (c₁ : ℝ) / Q)|
          + |4 * (Real.arctan 239⁻¹ - (c₂ : ℝ) / Q)| := by
        exact abs_sub _ _
    _ = 16 * |Real.arctan 5⁻¹ - (c₁ : ℝ) / Q|
          + 4 * |Real.arctan 239⁻¹ - (c₂ : ℝ) / Q| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ 16 * (1 / D) + 4 * (1 / D) := by gcongr
    _ = 20 / D := by ring
    _ ≤ 1 / E := by rw [div_le_div_iff₀ hDr hEr, one_mul]; exact_mod_cast hDE

end BSN
