/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Basic
public import Fast.Lit

/-!
# Metaprogram helpers and the general rational recogniser

The closed-numeral evaluators `evalNat`/`evalRealAsNat`, and `recognizeRat`, which reads a
rational surface literal (integer, fraction, decimal, `ℕ`-exponent power, and their negatives) as
`(neg, num, den)` with a proof `e = sfrac neg num den`. Re-exports `Fast.Lit`.
-/
@[expose] public section


namespace BSN
open Enclosure

open Lean Elab Meta

/-! ### Shared metaprogram helpers -/

/-- The value of a closed `ℕ` expression, read off its arithmetic structure, with `whnf` only as a
fallback for a non-canonical head. -/
meta partial def evalNat (e : Expr) : MetaM ℕ := do
  if let .lit (.natVal k) := e then return k
  if let some k := e.nat? then return k
  match_expr e with
  | OfNat.ofNat _ n _ => evalNat n
  | HAdd.hAdd _ _ _ _ a b => return (← evalNat a) + (← evalNat b)
  | HMul.hMul _ _ _ _ a b => return (← evalNat a) * (← evalNat b)
  | HSub.hSub _ _ _ _ a b => return (← evalNat a) - (← evalNat b)
  | HDiv.hDiv _ _ _ _ a b => return (← evalNat a) / (← evalNat b)
  | HPow.hPow _ _ _ _ a b => return (← evalNat a) ^ (← evalNat b)
  | Nat.succ a => return (← evalNat a) + 1
  | Nat.zero => return 0
  | _ =>
    let e' ← whnf e
    if e' == e then throwError "evalNat: not a closed Nat: ctor={e.ctorName} expr={e}"
    evalNat e'

/-- The `ℕ` value of a closed real numeral expression (`OfNat`, `^`, `*`, `+`, `ℕ`-casts). -/
meta partial def evalRealAsNat (e : Expr) : MetaM ℕ := do
  match_expr e with
  | OfNat.ofNat _ n _ => evalNat n
  | HPow.hPow _ _ _ _ a b => return (← evalRealAsNat a) ^ (← evalNat b)
  | HMul.hMul _ _ _ _ a b => return (← evalRealAsNat a) * (← evalRealAsNat b)
  | HAdd.hAdd _ _ _ _ a b => return (← evalRealAsNat a) + (← evalRealAsNat b)
  | Nat.cast _ _ a => evalNat a
  | _ => throwError "evalRealAsNat: cannot read a Nat from {e}"

/-! ### The recogniser -/

/-- Fails unless a power's exponent type `β` is `ℕ`, with a dedicated error for a `ℝ` exponent
(`Real.rpow`). -/
meta def checkNatExponent (β e : Expr) : MetaM Unit := do
  if β.isConstOf ``Real then
    throwError "recognizeRat: {e} is a real-exponent power (`Real.rpow`), not a rational \
      literal; write the exponent as a natural number, e.g. `x ^ (60 : ℕ)`"
  unless β.isConstOf ``Nat do
    throwError "recognizeRat: unsupported exponent type {β} in {e}"

/-- The `sfrac_pow_eq` application: a proof `a ^ b = sfrac neg' (u^n) (v^n)` from
`pf : a = sfrac neg u v`, where `n` is the value of the exponent expression `b` and
`neg' = neg && n odd`. -/
meta def mkPowEqPf (a b pf : Expr) (neg neg' : Bool) (u v n : ℕ) : Expr :=
  mkAppN (mkConst ``sfrac_pow_eq)
    #[a, toExpr neg, toExpr neg', natLitShared u, natLitShared v, b, natLitShared (u ^ n),
      natLitShared (v ^ n),
      pf, reflBoolTrue, reflBoolTrue, reflBoolTrue]

/-- Recognise a signed integer real literal `e` as `(neg, num, pf : e = sfrac neg num 1)`.
Handles `0`, `1`, numerals `≥ 2`, `Nat.cast`, `ℕ`-exponent powers of these (e.g. the `10 ^ 45`
inside a `1 / 10 ^ 45` bound), and their negations. -/
meta partial def recognizeInt (e : Expr) : MetaM (Bool × ℕ × Expr) := do
  match_expr e with
  | Neg.neg _ _ inner =>
    let (neg, n, pf) ← recognizeInt inner
    return (!neg, n,
      mkAppN (mkConst ``sfrac_neg_eq) #[inner, toExpr neg, natLitShared n, natLitShared 1, pf])
  | HPow.hPow _ β _ _ a b =>
    checkNatExponent β e
    let (neg, u, pf) ← recognizeInt a
    let n ← evalNat b
    let neg' := neg && n % 2 == 1
    return (neg', u ^ n, mkPowEqPf a b pf neg neg' u 1 n)
  | _ =>
    let k ← evalRealAsNat e
    let pf := if k == 0 then mkConst ``sfrac_zero_eq
              else if k == 1 then mkConst ``sfrac_one_eq
              else mkApp (mkConst ``sfrac_natCast) (natLitShared k)
    return (false, k, pf)

/-- Recognise a `ℚ`-valued expression `q̂` as `(neg, num, den, pf : ((q̂ : ℚ) : ℝ) = sfrac neg num
den)`. Handles the dyadic shapes of `mkNatDyadic` and `mkSignedDyadic`, their negations, and named
`ℚ` constants (unfolded). -/
meta partial def recognizeRatCastQ (q : Expr) : MetaM (Bool × ℕ × ℕ × Expr) := do
  match_expr q with
  | Neg.neg _ _ inner =>
    let (neg, num, den, pf) ← recognizeRatCastQ inner
    return (!neg, num, den,
      mkAppN (mkConst ``sfrac_ratCast_neg) #[inner, toExpr neg, natLitShared num,
            natLitShared den, pf])
  | HDiv.hDiv _ _ _ _ num den => do
    let Q ← match_expr den with
      | Nat.cast _ _ QE => evalNat QE
      | _ => throwError "recognizeRatCastQ: expected a `↑Q` denominator, got {den}"
    match_expr num with
    | Nat.cast _ _ pE =>
      let p ← evalNat pE
      return (false, p, Q,
              mkApp2 (mkConst ``sfrac_ratCast_natDiv) (natLitShared p) (natLitShared Q))
    | Int.cast _ _ iE =>
      let_expr HSub.hSub _ _ _ _ ma mb := iE
        | throwError "recognizeRatCastQ: expected a `↑mp - ↑mn` numerator, got {iE}"
      let mp ← match_expr ma with
        | Nat.cast _ _ mE => evalNat mE
        | _ => throwError "recognizeRatCastQ: expected `↑mp`, got {ma}"
      let mn ← match_expr mb with
        | Nat.cast _ _ mE => evalNat mE
        | _ => throwError "recognizeRatCastQ: expected `↑mn`, got {mb}"
      if mn ≤ mp then
        return (false, mp - mn, Q, mkAppN (mkConst ``sfrac_ratCast_intSub_nonneg)
          #[natLitShared mp, natLitShared mn, natLitShared Q, reflBoolTrue])
      else
        return (true, mn - mp, Q, mkAppN (mkConst ``sfrac_ratCast_intSub_neg)
          #[natLitShared mp, natLitShared mn, natLitShared Q, reflBoolTrue])
    | _ => throwError "recognizeRatCastQ: unsupported ℚ numerator {num}"
  | _ =>
    if let some q' ← unfoldDefinition? q then
      recognizeRatCastQ q'
    else
      throwError "recognizeRatCastQ: unsupported ℚ value {q}"

/-- Recognise any signed rational real literal `e` as `(neg, num, den, pf : e = sfrac neg num
den)`. Handles integers, fractions of integers, decimals, casts of `ℚ` dyadic values (named
`*_approx` constants included), `ℕ`-exponent powers of any of these (`10 ^ 60`, `(3/2) ^ 5`,
`(-2) ^ 7`), and their negations. -/
meta partial def recognizeRat (e : Expr) : MetaM (Bool × ℕ × ℕ × Expr) := do
  match_expr e with
  | Rat.cast _ _ q => recognizeRatCastQ q
  | Neg.neg _ _ inner =>
    let (neg, num, den, pf) ← recognizeRat inner
    return (!neg, num, den,
      mkAppN (mkConst ``sfrac_neg_eq) #[inner, toExpr neg, natLitShared num, natLitShared den, pf])
  | HPow.hPow _ β _ _ a b =>
    checkNatExponent β e
    let (neg, u, v, pf) ← recognizeRat a
    let n ← evalNat b
    let neg' := neg && n % 2 == 1
    return (neg', u ^ n, v ^ n, mkPowEqPf a b pf neg neg' u v n)
  | HDiv.hDiv _ _ _ _ na nb =>
    let (aneg, an, apf) ← recognizeInt na
    let (bneg, bn, bpf) ← recognizeInt nb
    let pf := mkAppN (mkConst ``sfrac_div_eq)
      #[na, nb, natLitShared an, natLitShared bn, toExpr aneg, toExpr bneg, apf, bpf]
    return (aneg != bneg, an, bn, pf)
  | OfScientific.ofScientific _ _ mE sE eE =>
    unless sE.isConstOf ``Bool.true do
      throwError "recognizeRat: only negative-exponent decimal literals are supported"
    let m ← evalNat mE
    let ee ← evalNat eE
    let v := 10 ^ ee
    return (false, m, v,
      mkAppN (mkConst ``sfrac_ofScientific_eq) #[natLitShared m, natLitShared ee, natLitShared v,
            reflBoolTrue])
  | _ =>
    let (neg, k, pf) ← recognizeInt e
    return (neg, k, 1, pf)

end BSN
