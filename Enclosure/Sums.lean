module

public import Enclosure.Core
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Real interval enclosures: finite-sum helpers

`Finset.Ico`/`range` splitting lemmas and enclosure transport along equalities, used to assemble
an enclosure of a finite sum term by term.
-/
@[expose] public section


namespace Enclosure

/-! ### Transport and finite-sum helpers -/

/-- Transport an enclosure along an equality of the enclosed real. -/
theorem Real.IsNear.of_eq {x y : ℝ} {n : Bool} {cn cd rn rd : ℕ}
    (he : x = y) (h : Real.IsNear y n cn cd rn rd) : Real.IsNear x n cn cd rn rd := by
  rw [he]; exact h

/-- Split a `Finset.Ico` sum at a midpoint `m ∈ [a,b]` (both bounds as `Nat.ble` reflections). -/
theorem sum_Ico_consec_real (f : ℕ → ℝ) (a m b : ℕ)
    (hab : Nat.ble a m = true) (hmb : Nat.ble m b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = (∑ i ∈ Finset.Ico a m, f i) + (∑ i ∈ Finset.Ico m b, f i) :=
  (Finset.sum_Ico_consecutive f (Nat.le_of_ble_eq_true hab) (Nat.le_of_ble_eq_true hmb)).symm

/-- A width-one `Finset.Ico` sum (`b = a+1`) is the single term `f a`. -/
theorem sum_Ico_width_one_real (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq b (a.add 1) = true) :
    (∑ i ∈ Finset.Ico a b, f i) = f a := by
  have hb : b = a + 1 := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.sum_Ico_succ_top (Nat.le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]

/-- An empty `Finset.Ico` sum (`a = b`) is `0`, enclosed with radius `0`. -/
theorem Real.IsNear.sum_Ico_empty (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq a b = true) :
    Real.IsNear (∑ i ∈ Finset.Ico a b, f i) false (nat_lit 0) (nat_lit 1) (nat_lit 0)
      (nat_lit 1) := by
  have hb : a = b := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.Ico_self, Finset.sum_empty]
  simp [Real.IsNear, sfrac]

/-- A `Finset.range n` sum as a `Finset.Ico 0 n` sum. -/
theorem sum_range_eq_Ico_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.Ico 0 n, f i) := by
  rw [Finset.range_eq_Ico]

end Enclosure
