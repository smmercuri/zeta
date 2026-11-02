module

public import Enclosure.Sfrac
public import Enclosure.Defs

/-!
# Real interval enclosures: the `Real.IsNear` predicate

`Real.IsNear x neg cn cd rn rd` says `|x − ±cn/cd| ≤ rn/rd`: `x` within radius `rn/rd` of the signed
centre `±cn/cd`. Centre and radius are ratios of naturals with the sign a separate `Bool`.
-/
@[expose] public section


namespace Enclosure

/-- `|x − ±cn/cd| ≤ rn/rd`: `x` is within radius `rn/rd` of the signed centre `sfrac neg cn cd`. -/
def Real.IsNear (x : ℝ) (neg : Bool) (cn cd rn rd : ℕ) : Prop :=
  |x - sfrac neg cn cd| ≤ (rn : ℝ) / rd

/-- The lower endpoint of an `IsNear` enclosure: `sfrac neg cn cd − rn/rd ≤ x`. -/
theorem Real.IsNear.lower {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : sfrac neg cn cd - (rn : ℝ) / rd ≤ x := by
  have := (abs_le.mp h).1; linarith

/-- The upper endpoint of an `IsNear` enclosure: `x ≤ sfrac neg cn cd + rn/rd`. -/
theorem Real.IsNear.upper {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : x ≤ sfrac neg cn cd + (rn : ℝ) / rd := by
  have := (abs_le.mp h).2; linarith

/-- Build an `IsNear` enclosure from the two endpoint inequalities. -/
theorem Real.IsNear.mk' {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (hlo : sfrac neg cn cd - (rn : ℝ) / rd ≤ x) (hhi : x ≤ sfrac neg cn cd + (rn : ℝ) / rd) :
    Real.IsNear x neg cn cd rn rd := abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Signed numerator as a difference of natural parts

`numPos`/`numNeg` (one always `0`) write `sfrac neg cn cd` as `(numPos − numNeg)/cd`. -/

/-- `sfrac` as the difference of its natural parts over the denominator. -/
theorem sfrac_eq_parts (neg : Bool) (cn cd : ℕ) :
    sfrac neg cn cd = ((numPos neg cn : ℝ) - (numNeg neg cn : ℝ)) / cd := by
  cases neg <;> simp [sfrac, numPos, numNeg, neg_div, sub_zero, zero_sub]

/-- The absolute value of a signed fraction is its (nonnegative) magnitude. -/
theorem abs_sfrac (neg : Bool) (cn cd : ℕ) : |sfrac neg cn cd| = (cn : ℝ) / cd := by
  rw [sfrac]
  cases neg <;> simp [abs_div, abs_of_nonneg]

/-- The product of two signed fractions: signs `xor`, magnitudes multiply. -/
theorem sfrac_mul (nx ny : Bool) (cnx cdx cny cdy : ℕ) :
    sfrac nx cnx cdx * sfrac ny cny cdy = sfrac (Bool.xor nx ny) (cnx * cny) (cdx * cdy) := by
  cases nx <;> cases ny <;> simp [sfrac] <;> ring

/-! ### Constants and radius weakening -/

/-- A signed rational encloses itself with radius `0`. -/
theorem Real.IsNear.const (neg : Bool) (cn cd : ℕ) :
    Real.IsNear (sfrac neg cn cd) neg cn cd (nat_lit 0) (nat_lit 1) := by
  simp [Real.IsNear]

/-- Radius weakening: any enclosure stays valid with a larger radius `rn'/rd' ≥ rn/rd`. -/
theorem Real.IsNear.widen {x : ℝ} {n : Bool} {cn cd rn rd rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd) (hrd : Nat.ble 1 rd) (hrd' : Nat.ble 1 rd')
    (hle : Nat.ble (rn.mul rd') (rn'.mul rd)) :
    Real.IsNear x n cn cd rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hle
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  simp only [Real.IsNear] at h ⊢
  refine le_trans h ?_
  rw [div_le_div_iff₀ hrdR hrd'R]
  exact_mod_cast hle

end Enclosure
