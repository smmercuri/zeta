module

public import Bernoulli.FoldExperiment

/-!
# Exact Bernoulli numerators via tangent numbers

Rearranging the closed form `tangentNumber_eq`, an even Bernoulli number is an explicit integer
fraction built from a tangent number:
`B_{2m+2} = A / B`,  with  `A = (-1)^m·(2m+2)·T_{m+1}`,  `B = 2^{2m+2}·(2^{2m+2}-1)`.
`num_eq_of_eq_intDiv` turns this into the reduced numerator once a candidate `p / q` is supplied and
validated by the integer identities `p·B = q·A` and `gcd = 1`.

This module emits the shared data the downstream development reads by reference: the tangent numbers
`T₀..T₉₉` (`tangentNumberLit_k`) and the reduced numerators `num(B₂)..num(B₁₉₈)` (`bernNumLit_m`),
each a standalone environment lemma generated in `MetaM`, every side condition a `reflBoolTrue`.
The reduced numerators feed the regular-prime sweeps in `Bernoulli.Kummer`.

The full rational values `bernoulli n = p / q` and the `derive_bernoulli` generator live in
`Bernoulli.BernoulliExact`.  No `native_decide`.
-/
@[expose] public section


open scoped Nat

namespace TangentNumbers

/-! ## The exact reduced value -/

/-- If `A/B = p/q` with `q > 0` and `p, q` coprime, then `p` is the reduced numerator of `A/B`. -/
theorem num_eq_of_eq_intDiv {A B p q : ℤ} (hB : B ≠ 0) (hq : 0 < q)
    (hcop : Int.gcd p q = 1) (hcross : p * B = q * A) :
    ((A : ℚ) / (B : ℚ)).num = p := by
  have heq : (A : ℚ) / (B : ℚ) = (p : ℚ) / (q : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast hB) (by exact_mod_cast hq.ne')]
    have : A * q = p * B := by linear_combination -hcross
    exact_mod_cast this
  rw [heq]
  exact Rat.num_div_eq_of_coprime hq hcop

open PowerSeries in
/-- `B_{2m+2}` as an explicit integer fraction using the tangent number `T_{m+1}`. -/
theorem bernoulli_eq_tangent_intDiv (m : ℕ) :
    bernoulli (2 * m + 2) =
      (((-1) ^ m * (2 * m + 2) * (tangentNumber (m + 1) : ℤ) : ℤ) : ℚ) /
        (((2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) : ℚ)) := by
  have h := tangentNumber_eq m
  have hfac : ((2 * m + 2)! : ℚ) = (2 * m + 2) * (2 * m + 1)! := by
    have hidx : 2 * m + 2 = (2 * m + 1) + 1 := rfl
    rw [hidx, Nat.factorial_succ]
    push_cast
    ring
  have hP : (2 : ℚ) ^ (2 * m + 2) ≠ 0 := by positivity
  have hQ : (2 : ℚ) ^ (2 * m + 2) - 1 ≠ 0 := by
    have h1 : (1 : ℚ) < 2 ^ (2 * m + 2) := one_lt_pow₀ (by norm_num) (by positivity)
    linarith
  have hfac' : ((2 * m + 1)! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hfac] at h
  push_cast at h ⊢
  rw [h]
  field_simp
  have hs : (((-1 : ℚ)) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hs, mul_one]

theorem intDenom_ne_zero (m : ℕ) : (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) ≠ 0 :=
  mul_ne_zero (by positivity) (sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) (by omega)).ne')

/-! ## Per-`m` certificate: the reduced numerator from a tangent number

`bernoulli_num_of` gives the reduced numerator of `B_{2m+2}` from its tangent number `Tₙ` and a
candidate `p/q`, with the validating identities as kernel `decide`s (each a `reflBoolTrue`). -/

/-- The reduced numerator of `B_{2m+2}` is `p`, from the tangent number and a validated `p/q`. -/
theorem bernoulli_num_of (m : ℕ) (Tn : ℕ) (p q : ℤ)
    (hT : tangentNumber (m + 1) = Tn)
    (hq : decide (0 < q) = true)
    (hcop : (Int.gcd p q).beq 1 = true)
    (hcross : decide (p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
                = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ))) = true) :
    (bernoulli (2 * m + 2)).num = p := by
  have hq' : 0 < q := of_decide_eq_true hq
  have hcop' : Int.gcd p q = 1 := Nat.eq_of_beq_eq_true hcop
  have hcross' : p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
      = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ)) := of_decide_eq_true hcross
  have hTn : (tangentNumber (m + 1) : ℤ) = (Tn : ℤ) := by rw [hT]
  rw [bernoulli_eq_tangent_intDiv m, hTn]
  exact num_eq_of_eq_intDiv (intDenom_ne_zero m) hq' hcop' hcross'

/-- `|num(B_{2m+2})| = n` from the reduced numerator `p` and `|p| = n` (checked once, as a
`Nat.beq`). The regular-prime sweep tests divisibility on this `Nat` literal, so `natAbs` is reduced
once per `m` here rather than per prime. -/
theorem numAbs_of (m n : ℕ) (p : ℤ) (hnum : (bernoulli (2 * m + 2)).num = p)
    (hn : p.natAbs.beq n = true) : (bernoulli (2 * m + 2)).num.natAbs = n := by
  rw [hnum]; exact Nat.eq_of_beq_eq_true hn

/-! ## The shared numerator lemmas

`fold_emit_tangent_numbers` (from `Bernoulli.FoldExperiment`) puts
`tangentNumberLit_k : tangentNumber k = Tₖ` in the environment.  `emit_bernoulli_numerators N` then
emits, for `m = 0, …, N-1`, the reduced numerator `bernNumLit_m : (bernoulli (2m+2)).num = pₘ` —
each read straight off `tangentNumberLit_{m+1}` (its value taken from the lemma's statement) plus
one `bernoulli_num_of` with the validating identities as `reflBoolTrue`s.  The `bernNumLit_m` are
what `Bernoulli.Kummer` reads.  No `native_decide`. -/
open Lean Lean.Meta Lean.Elab Lean.Elab.Command in
elab "emit_bernoulli_numerators " nStx:num : command => liftTermElabM do
  let N := nStx.getNat
  let intTy := Expr.const ``Int []
  for m in [0:N] do
    let hT : Expr := .const (`TangentNumbers ++ Name.mkSimple s!"tangentNumberLit_{m + 1}") []
    let some (_, _, TvalE) := (← inferType hT).eq?
      | throwError "emit_bernoulli_numerators: tangentNumberLit_{m + 1} is not an equality"
    let some Tval := TvalE.rawNatLit?
      | throwError "emit_bernoulli_numerators: tangent value is not a numeral"
    let sign : Int := if m % 2 == 0 then 1 else -1
    let A : Int := sign * (2 * m + 2) * (Tval : Int)
    let bden : Int := 2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)
    let g : Nat := Int.gcd A bden
    let pE := Lean.toExpr (A / g)
    let pf := mkAppN (.const ``TangentNumbers.bernoulli_num_of [])
      #[mkRawNatLit m, TvalE, pE, Lean.toExpr (bden / g), hT, reflBoolTrue, reflBoolTrue,
        reflBoolTrue]
    let stmt := mkApp3 (.const ``Eq [Level.one]) intTy
      (mkApp (.const ``Rat.num []) (mkApp (.const ``bernoulli []) (mkRawNatLit (2 * m + 2)))) pE
    let litNm := `TangentNumbers ++ Name.mkSimple s!"bernNumLit_{m}"
    addDecl (.thmDecl { name := litNm, levelParams := [], type := stmt, value := pf })
    -- `bernNumAbs_m : num.natAbs = n` — the `Nat` literal the sweep reads (natAbs done once here)
    let n := (A / g).natAbs
    let absStmt := mkApp3 (.const ``Eq [Level.one]) (.const ``Nat [])
      (mkApp (.const ``Int.natAbs [])
            (mkApp (.const ``Rat.num [])
              (mkApp (.const ``bernoulli []) (mkRawNatLit (2 * m + 2))))) (mkRawNatLit n)
    let absPf :=
        mkAppN (.const ``TangentNumbers.numAbs_of []) #[mkRawNatLit m, mkRawNatLit n, pE,
          .const litNm [], reflBoolTrue]
    addDecl (.thmDecl
      { name := `TangentNumbers ++ Name.mkSimple s!"bernNumAbs_{m}", levelParams := [],
        type := absStmt, value := absPf })

fold_emit_tangent_numbers 99
emit_bernoulli_numerators 99

/-- Sanity checks: the emitted lemmas certify the known tangent numbers and Bernoulli numerators. -/
example : tangentNumber 8 = 1903757312 := tangentNumberLit_8
example : (bernoulli 12).num = -691 := bernNumLit_5
example : (bernoulli 20).num = -174611 := bernNumLit_9

end TangentNumbers
