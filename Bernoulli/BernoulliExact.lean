import Bernoulli.BernoulliValues

/-!
# Exact rational Bernoulli numbers, and a lemma generator

The exact-value layer on top of `Bernoulli.BernoulliValues`: whereas that module certifies the
reduced *numerators* (for the regular-prime sweeps), here we produce the full rational values
`bernoulli n = p / q`.

`bernoulli_even_div` reads an even Bernoulli number off its tangent number as a reduced fraction,
once a candidate `p / q` is supplied and validated by the integer identity `p·B = q·A` (`q > 0`);
the `0`, `1` and odd entries reuse Mathlib's `bernoulli_zero`, `bernoulli_one`,
`bernoulli_eq_zero_of_odd`.

The `derive_bernoulli N` command materialises `bernoulli_0, …, bernoulli_N`, each a lemma
`bernoulli n = p / q` with `p / q` displayed in clean `ℚ` numerals: the even entries read their
tangent number off the `tangentNumberLit_k` lemmas (emitted by `Bernoulli.TangentVerify`, so
`N < 200`), with the reduced `p / q` computed in `MetaM` and every side condition a kernel-checked
`reflBoolTrue`.  No `native_decide`.
-/

open scoped Nat

namespace TangentNumbers

/-- `B_{2m+2} = p / q`, from the tangent number and a validated `p·B = q·A` (`q > 0`).  Reduction is
not needed for the equality, but the generator supplies the reduced `p/q`. -/
theorem bernoulli_even_div (m : ℕ) (Tn : ℕ) (p q : ℤ)
    (hT : tangentNumber (m + 1) = Tn)
    (hq : decide (0 < q) = true)
    (hcross : decide (p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
                = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ))) = true) :
    bernoulli (2 * m + 2) = (p : ℚ) / (q : ℚ) := by
  have hq' : (0 : ℤ) < q := of_decide_eq_true hq
  have hcross' : p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
      = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ)) := of_decide_eq_true hcross
  have hTn : (tangentNumber (m + 1) : ℤ) = (Tn : ℤ) := by rw [hT]
  rw [bernoulli_eq_tangent_intDiv m, hTn,
    div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m) (by exact_mod_cast hq'.ne')]
  have : ((-1) ^ m * (2 * m + 2) * (Tn : ℤ)) * q
      = p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) := by
    rw [mul_comm]
    exact hcross'.symm
  exact_mod_cast this

/-- `B_0 = 1 / 1`. -/
theorem bernoulli_zero_div : bernoulli 0 = ((1 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by
  rw [bernoulli_zero]; norm_num

/-- `B_1 = -1 / 2`. -/
theorem bernoulli_one_div : bernoulli 1 = ((-1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by
  rw [bernoulli_one]; norm_num

/-- `B_{2m+3} = 0 / 1` (the odd Bernoulli numbers past `1` vanish). -/
theorem bernoulli_odd_div (m : ℕ) : bernoulli (2 * m + 3) = ((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := by
  rw [bernoulli_eq_zero_of_odd ⟨m + 1, by ring⟩ (by omega)]; norm_num

/-! ## The generator

`derive_bernoulli N` adds `bernoulli_0, …, bernoulli_N`, each `bernoulli n = p / q` with `p / q` a
reduced rational displayed with clean `ℚ` numerals (e.g. `bernoulli 12 = -691 / 2730`).  The proof
carries `ℤ`-cast numerals, which are `rfl`-defeq to the stated `ℚ` numerals. -/
open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term in
elab "derive_bernoulli " nStx:num : command => do
  let N := nStx.getNat
  liftTermElabM do
    if 200 ≤ N then throwError "derive_bernoulli: N must be < 200 (the emitted tangent range)"
    let curNs ← getCurrNamespace
    let ratTy := Expr.const ``Rat []
    for n in [0:N + 1] do
      -- reduced `p / q` and its proof, by case
      let mut p : Int := 0
      let mut q : Int := 1
      let mut proof : Expr := default
      if n == 0 then
        p := 1; proof := .const ``TangentNumbers.bernoulli_zero_div []
      else if n == 1 then
        p := -1; q := 2; proof := .const ``TangentNumbers.bernoulli_one_div []
      else if n % 2 == 1 then
        proof := mkApp (.const ``TangentNumbers.bernoulli_odd_div []) (mkRawNatLit ((n - 3) / 2))
      else
        let m := (n - 2) / 2
        let hT : Expr := .const (`TangentNumbers ++ Name.mkSimple s!"tangentNumberLit_{m + 1}") []
        let some (_, _, Tlit) := (← inferType hT).eq?
          | throwError "derive_bernoulli: tangentNumberLit_{m + 1} is not an equality"
        let some Tval := Tlit.rawNatLit?
          | throwError "derive_bernoulli: tangent value is not a numeral"
        let sign : Int := if m % 2 == 0 then 1 else -1
        let A : Int := sign * (2 * m + 2) * (Tval : Int)
        let bden : Int := 2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)
        let gcdN : Nat := Int.gcd A bden
        p := A / gcdN; q := bden / gcdN
        proof := mkAppN (.const ``TangentNumbers.bernoulli_even_div [])
          #[mkRawNatLit m, Tlit, Lean.toExpr p, Lean.toExpr q, hT, reflBoolTrue, reflBoolTrue]
      -- clean `ℚ` numerals for the statement
      let pStx ← if p < 0 then `(-$(Lean.quote p.natAbs)) else `($(Lean.quote p.natAbs))
      let rhs ← elabTermAndSynthesize (← `(($pStx : ℚ) / ($(Lean.quote q.natAbs) : ℚ))) (some ratTy)
      let stmt ← mkEq (mkApp (.const ``bernoulli []) (mkRawNatLit n)) rhs
      let nm := curNs ++ Name.mkSimple ("bernoulli_" ++ toString n)
      addDecl (.thmDecl { name := nm, levelParams := [], type := stmt, value := proof })

/-! ### Demo: `bernoulli_0, …, bernoulli_20` -/

derive_bernoulli 20

example : bernoulli 4 = ((-1 : ℤ) : ℚ) / ((30 : ℤ) : ℚ) := bernoulli_4
example : bernoulli 12 = ((-691 : ℤ) : ℚ) / ((2730 : ℤ) : ℚ) := bernoulli_12
example : bernoulli 7 = ((0 : ℤ) : ℚ) / ((1 : ℤ) : ℚ) := bernoulli_7

end TangentNumbers
