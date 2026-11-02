module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Module

/-!
# The signed rational `sfrac`

The signed rational `sfrac neg cn cd = ±cn/cd` (centre and radius are ratios of naturals with the
sign a separate `Bool`) and its recasting/positivity lemmas. Each recasting lemma proves
`<surface form> = sfrac neg num den`, so together they form the vocabulary of the rational
recogniser and the endpoint representation used by the interval-enclosure layer.

This module depends only on Mathlib. It is the base of the `Enclosure` namespace: the
interval-arithmetic layer (`Enclosure.*`) builds directly on it, and the binary-split engine
(`Enclosure.BinarySplit.Basic`) opens `Enclosure` for the `sfrac` vocabulary.
-/
@[expose] public section


namespace Enclosure

/-! ### The signed rational `sfrac` -/

/-- The real value of a sign-flagged natural fraction: `−cn/cd` when `neg`, else `cn/cd`. -/
noncomputable def sfrac (neg : Bool) (cn cd : ℕ) : ℝ := (if neg then -1 else 1) * ((cn : ℝ) / cd)

/-- Flipping the sign flag negates the signed fraction. -/
theorem sfrac_not (neg : Bool) (cn cd : ℕ) : sfrac (!neg) cn cd = - sfrac neg cn cd := by
  cases neg <;> simp [sfrac]

/-- A `false`-signed fraction is the bare quotient `↑cn/↑cd` (the form the certificate lemmas
emit). -/
theorem sfrac_false_div (cn cd : ℕ) : sfrac false cn cd = (cn : ℝ) / cd := by simp [sfrac]

/-- A `true`-signed fraction is the negated quotient `(-↑cn)/↑cd` (the form the reciprocal
certificate lemmas emit for a negative argument). -/
theorem sfrac_true_div (cn cd : ℕ) : sfrac true cn cd = (-(cn : ℝ)) / cd := by simp [sfrac, neg_div]

/-- Decimal literal `OfScientific m true e` (`= m·10⁻ᵉ`) as the fraction `↑m/↑v` with `v = 10^e`. -/
theorem ofScientific_dyadic_arg (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = (m : ℝ) / (v : ℝ) := by
  have hv : 10 ^ e = v := Nat.eq_of_beq_eq_true hv
  subst hv
  rw [← Rat.cast_ofScientific, Rat.ofScientific_def_eq_if]
  simp

/-! ### Recasting lemmas (each proves `<surface> = sfrac neg num den`) -/

/-- Integer atom in `Nat.cast` form: `↑n = sfrac false n 1`. Used for numerals `≥ 2` (whose `↑n` is
defeq to the goal's `OfNat` literal) and for `Nat.cast` arguments. -/
theorem sfrac_natCast (n : ℕ) : (n : ℝ) = sfrac false n 1 := by simp [sfrac]

/-- The literal `0`, kept as the goal's `OfNat` form. -/
theorem sfrac_zero_eq : (0 : ℝ) = sfrac false (nat_lit 0) (nat_lit 1) := by simp [sfrac]

/-- The literal `1`, kept as the goal's `OfNat` form. -/
theorem sfrac_one_eq : (1 : ℝ) = sfrac false (nat_lit 1) (nat_lit 1) := by simp [sfrac]

/-- Negation flips the sign flag. -/
theorem sfrac_neg_eq (x : ℝ) (neg : Bool) (num den : ℕ) (h : x = sfrac neg num den) :
    -x = sfrac (!neg) num den := by rw [h, sfrac_not]

/-- A quotient of two signed integers `±an / ±bn` is the signed fraction with `xor`-ed sign. -/
theorem sfrac_div_eq (na nb : ℝ) (an bn : ℕ) (aneg bneg : Bool)
    (hn : na = sfrac aneg an 1) (hd : nb = sfrac bneg bn 1) :
    na / nb = sfrac (aneg != bneg) an bn := by
  rw [hn, hd]
  cases aneg <;> cases bneg <;> simp [sfrac] <;> ring

/-- A decimal literal `OfScientific m true e` (`= m·10⁻ᵉ`, `v = 10^e`) as `sfrac false m v`. -/
theorem sfrac_ofScientific_eq (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = sfrac false m v := by
  rw [ofScientific_dyadic_arg m e v hv]; simp [sfrac]

/-- `0 < n` (in `ℕ`) from a kernel `Nat.ble 1 n` side condition (`Nat.blt 0 n` unfolds to
exactly `Nat.ble 1 n`, so the conditions are stated as `ble` to save the kernel one unfold
per evaluation). -/
theorem pos_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)

/-- `(0:ℝ) < n` from a kernel `Nat.ble 1 n` side condition (`Nat.blt 0 n` unfolds to
exactly `Nat.ble 1 n`, so the conditions are stated as `ble` to save the kernel one
unfold per evaluation). -/
theorem pos_real_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : (0 : ℝ) < n := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)

/-- Strict comparison of two nonnegative rational-literal reals through their `sfrac` forms:
one cross-multiplied `Nat.blt`, kernel-evaluated. The certificate bundles' interval-disjointness
chains are nested `List.IsChain.cons_cons` proof terms over this. -/
theorem dec_lt_dec {a b : ℝ} (an av bn bv : ℕ)
    (ha : a = sfrac false an av) (hb : b = sfrac false bn bv)
    (hav : Nat.ble 1 av = true) (hbv : Nat.ble 1 bv = true)
    (h : Nat.blt (an.mul bv) (bn.mul av) = true) : a < b := by
  subst ha hb
  simp only [Nat.blt_eq, Nat.mul_eq] at h
  rw [sfrac_false_div, sfrac_false_div,
    div_lt_div_iff₀ (pos_real_of_ble hav) (pos_real_of_ble hbv)]
  exact_mod_cast h

/-- The `≤` twin of `dec_lt_dec`: one cross-multiplied `Nat.ble`. Term-level replacement for
the generated `non_empty := by norm_num` fields. -/
theorem dec_le_dec {a b : ℝ} (an av bn bv : ℕ)
    (ha : a = sfrac false an av) (hb : b = sfrac false bn bv)
    (hav : Nat.ble 1 av = true) (hbv : Nat.ble 1 bv = true)
    (h : Nat.ble (an.mul bv) (bn.mul av) = true) : a ≤ b := by
  subst ha hb
  simp only [Nat.ble_eq, Nat.mul_eq] at h
  rw [sfrac_false_div, sfrac_false_div,
    div_le_div_iff₀ (pos_real_of_ble hav) (pos_real_of_ble hbv)]
  exact_mod_cast h

/-- A nonnegative `sfrac` literal: term-level replacement for the generated
`left_nonneg := by norm_num` fields. -/
theorem dec_nonneg {a : ℝ} (an av : ℕ) (ha : a = sfrac false an av) : 0 ≤ a := by
  subst ha
  rw [sfrac_false_div]
  exact div_nonneg (Nat.cast_nonneg an) (Nat.cast_nonneg av)

/-- The real cast of a positive dyadic `ℚ` value `↑p/↑Q` (the shape `mkNatDyadic` emits and the
`*_approx%` value definitions carry) as `sfrac false p Q`. -/
theorem sfrac_ratCast_natDiv (p Q : ℕ) : (((p : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false p Q := by
  rw [sfrac_false_div]; push_cast; ring

/-- The real cast of a signed dyadic `ℚ` value `(↑mp − ↑mn)/↑Q` (the `mkSignedDyadic` shape) when
`mp ≥ mn`: sign `false`, magnitude `mp − mn`. -/
theorem sfrac_ratCast_intSub_nonneg (mp mn Q : ℕ) (hge : Nat.ble mn mp = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false (mp - mn) Q := by
  simp only [Nat.ble_eq] at hge
  rw [sfrac_false_div]; push_cast [Nat.cast_sub hge]; ring

/-- The real cast of a signed dyadic `ℚ` value `(↑mp − ↑mn)/↑Q` when `mp ≤ mn`: sign `true`,
magnitude `mn − mp`. -/
theorem sfrac_ratCast_intSub_neg (mp mn Q : ℕ) (hle : Nat.ble mp mn = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac true (mn - mp) Q := by
  simp only [Nat.ble_eq] at hle
  rw [sfrac_true_div]; push_cast [Nat.cast_sub hle]; ring

/-- The real cast of a negated `ℚ` value flips the sign flag of its recognised `sfrac` form. -/
theorem sfrac_ratCast_neg (q : ℚ) (neg : Bool) (num den : ℕ)
    (h : ((q : ℚ) : ℝ) = sfrac neg num den) : ((-q : ℚ) : ℝ) = sfrac (!neg) num den := by
  rw [sfrac_not, ← h]; push_cast; ring

/-- Natural power of a recognised rational: from `x = sfrac neg u v`, `x ^ n = sfrac neg' un vn`
with `un = u^n`, `vn = v^n` and the sign `neg' = neg && n odd`. Holds for every `u`, `v`, `n`,
including `v = 0` (both sides are then `0` for `n > 0`) and `n = 0` (both sides are `1`). -/
theorem sfrac_pow_eq (x : ℝ) (neg neg' : Bool) (u v n un vn : ℕ)
    (hx : x = sfrac neg u v)
    (hs : (Bool.xor neg' (Bool.and neg ((Nat.mod n 2).beq 1))).not = true)
    (hun : un.beq (Nat.pow u n) = true) (hvn : vn.beq (Nat.pow v n) = true) :
    x ^ n = sfrac neg' un vn := by
  obtain rfl : un = u ^ n := Nat.eq_of_beq_eq_true hun
  obtain rfl : vn = v ^ n := Nat.eq_of_beq_eq_true hvn
  subst hx
  have hdiv : ((u : ℝ) / v) ^ n = ((u ^ n : ℕ) : ℝ) / ((v ^ n : ℕ) : ℝ) := by
    push_cast
    rw [div_pow]
  cases neg with
  | false =>
    obtain rfl : neg' = false := by simpa using hs
    rw [sfrac_false_div, sfrac_false_div, hdiv]
  | true =>
    cases neg' with
    | true =>
      have hodd : Odd n := by
        have h1 : Nat.mod n 2 = 1 := Nat.eq_of_beq_eq_true (by simpa using hs)
        exact Nat.odd_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_true_div, neg_div, neg_div, hodd.neg_pow, hdiv]
    | false =>
      have heven : Even n := by
        have h1 : Nat.beq (Nat.mod n 2) 1 = false := by simpa using hs
        have h2 : n % 2 ≠ 1 := Nat.ne_of_beq_eq_false h1
        exact Nat.even_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_false_div, neg_div, heven.neg_pow, hdiv]

end Enclosure
