/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Basic
public import Enclosure
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Mathlib.Data.Nat.Log

/-!
# The proof-emitting metaprogram for `binarySplit`

`proveBS` computes the binary-split result tuple in `MetaM` and emits the
certificate lemmas of `Enclosure.BinarySplit.Basic` with concrete numeral literals, so the kernel
only verifies `Nat.beq` equalities on numerals. Also the helpers shared by every function tactic:
the dyadic denominator and `ℚ`-value `Expr` builders (`dyadicDenom`, `mkNatDyadic`,
`mkSignedDyadic`), the factorial-series term-count search `trigTermCountAux`, the aux-lemma lift
`mkBoundAux`, the even/odd certificate core `mkEvenOddCertCore` (`sin`/`cos`/`arctan`), and the
verifier assembler `mkVerifyLe`.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Per-process memo of `piVal`'s `(P, Q)` by precision `E`. Declared here rather than in
`Tactic.Pi` so it is initialized before `Tactic.Pi`'s `pi_near_*` constants elaborate. -/
initialize piValCache : IO.Ref (Std.HashMap Nat (Nat × Nat)) ← IO.mkRef ∅

/-- Memo caches for the leaf enclosures `√(N/M)` and `log(a/b)`, keyed by arguments and precision,
holding the `RNear` payload `(proof, x, neg, cn, cd, rn, rd)` as a tuple (`RNear` is defined
downstream). Declared here so they are initialized before `Tactic.Enclosures` elaborates. -/
initialize sqrtNearCache : IO.Ref (Std.HashMap (Nat × Nat × Nat)
      (Lean.Expr × Lean.Expr × Bool × Nat × Nat × Nat × Nat)) ← IO.mkRef ∅
initialize logNearCache : IO.Ref (Std.HashMap (Nat × Nat × Nat × Nat)
      (Lean.Expr × Lean.Expr × Bool × Nat × Nat × Nat × Nat)) ← IO.mkRef ∅

/-- One-slot memo for the `forCos`-independent part of the `sin`/`cos` range reduction: the
argument `(a, b, D)` and the packed result `(#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE, rcvE, hrc])`.
A single slot because `sin` and `cos` of the same argument are built consecutively and arguments
otherwise never repeat. -/
initialize trigReduceCache : IO.Ref (Option ((Nat × Nat × Nat) × (Array Nat × Array Lean.Expr))) ←
  IO.mkRef none

open Lean Elab Meta Tactic

/-! ### Shared real-value `Expr` builders

Builders for the enclosed real of a leaf or combinator, constructed directly in the form the
certificate lemmas conclude about rather than read back from a proof's type by `inferType`. -/

/-- The type `ℝ`. -/
meta def realTyE : Expr := mkConst ``Real

/-- `(↑n : ℝ)` (`@Nat.cast ℝ Real.instNatCast n`). -/
meta def mkNatCastR (n : ℕ) : Expr :=
  mkApp2 (mkConst ``Nat.cast [.zero]) realTyE (mkConst ``Real.instNatCast) |>.app (natLitShared n)

/-- `(↑u / ↑v : ℝ)`, in the elaborated form of the trig/exp/log certificate lemmas' arguments. -/
meta def mkCastDivR (u v : ℕ) : Expr :=
  mkAppN (mkConst ``HDiv.hDiv [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHDiv [.zero]) realTyE
        (mkApp2 (mkConst ``DivInvMonoid.toDiv [.zero]) realTyE (mkConst ``Real.instDivInvMonoid)),
      mkNatCastR u, mkNatCastR v]

/-- `-x` on `ℝ` (`@Neg.neg ℝ Real.instNeg x`). -/
meta def mkNegR (x : Expr) : Expr :=
  mkApp3 (mkConst ``Neg.neg [.zero]) realTyE (mkConst ``Real.instNeg) x

/-- `((-↑u) / ↑v : ℝ)`, in the elaborated form of the RHS of `sfrac_true_div`. -/
meta def mkNegCastDivR (u v : ℕ) : Expr :=
  mkAppN (mkConst ``HDiv.hDiv [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHDiv [.zero]) realTyE
        (mkApp2 (mkConst ``DivInvMonoid.toDiv [.zero]) realTyE (mkConst ``Real.instDivInvMonoid)),
      mkNegR (mkNatCastR u), mkNatCastR v]

/-- `sfrac neg cn cd : ℝ`, the LHS of `sfrac_false_div`/`sfrac_true_div` and the enclosed real of a
`Real.IsNear.const` leaf. -/
meta def mkSfracR (neg : Bool) (cn cd : ℕ) : Expr :=
  mkAppN (mkConst ``sfrac) #[toExpr neg, natLitShared cn, natLitShared cd]

/-- `fn x` for a unary real function constant `fn` such as `Real.exp`. -/
meta def mkRealFn (fn : Name) (x : Expr) : Expr := mkApp (mkConst fn) x

/-- The `ℕ` numeral `(n : ℕ)` in `OfNat.ofNat ℕ n (instOfNatNat n)` form. -/
private meta def mkNatOfNat (n : ℕ) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

/-- `(2 : ℝ)` in the elaborated `OfNat.ofNat ℝ 2 (instOfNatAtLeastTwo …)` form used by the `log2`
tier constants. -/
meta def mkRealTwo : Expr :=
  let atLeastTwo := mkApp2 (mkConst ``Nat.instAtLeastTwoHAddOfNat)
    (mkNatOfNat 1) (mkApp (mkConst ``Nat.instNeZeroSucc) (mkNatOfNat 0))
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) realTyE (mkRawNatLit 2)
    (mkApp4 (mkConst ``instOfNatAtLeastTwo [.zero]) realTyE (mkRawNatLit 2)
      (mkConst ``Real.instNatCast) atLeastTwo)

/-- The type `Real.IsNear x neg cn cd rn rd` with literal fields. -/
meta def mkIsNearTy (x : Expr) (neg : Bool) (cn cd rn rd : ℕ) : Expr :=
  mkAppN (mkConst ``Real.IsNear)
    #[x, toExpr neg, natLitShared cn, natLitShared cd, natLitShared rn, natLitShared rd]

/-- A constant referring to a new auxiliary lemma of type `ty` with proof `pf` (both
`instantiateMVars`'d). -/
meta def mkBoundAux (ty pf : Expr) : MetaM Expr := do
  let pf ← instantiateMVars pf
  let ty ← instantiateMVars ty
  return mkConst (← mkAuxLemma [] ty pf)

/-- The dyadic denominator for precision `1/D`: the least power of two `≥ 2·D`. -/
meta def dyadicDenom (D : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * D)

/-- `Nat.mul a b` (likewise `natAddE`, `natSuccE`, `natPowE`), spelled without the
`HMul`/`HAdd`/`HPow` instance indirection. -/
meta def natMulE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.mul) a b
meta def natAddE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.add) a b
meta def natSuccE (a : Expr) : Expr := mkApp (mkConst ``Nat.succ) a
meta def natPowE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.pow) a b

/-- A constant proving `e = v` for a closed `ℕ` expression `e`, as an auxiliary lemma deduplicated
by `mkAuxLemma`. -/
meta def mkNatEvalAux (e : Expr) (v : ℕ) : MetaM Expr := do
  let nm ← mkAuxLemma [] (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) e (natLitShared v))
    (mkApp2 (Expr.const ``Eq.refl [Level.one]) (mkConst ``Nat) (natLitShared v))
  return mkConst nm

/-- The least term count `M` (from the seed) for the `sin`/`cos` even/odd series whose tail guard
holds, with `L = u^k · 2D` and `R = v^k · k!` carried as running products. -/
partial def trigTermCountAux (u v M k L R : ℕ) : ℕ :=
  if u.blt ((k + 1) * v) && (2 * u ^ 2).ble ((k + 1) ^ 2 * v ^ 2)
      && (2 * L).ble R then M
  else trigTermCountAux u v (M + 1) (k + 4) (L * u ^ 4)
    (R * (v ^ 4 * ((k + 1) * (k + 2) * (k + 3) * (k + 4))))

/-- The signed dyadic rational `(((↑mp - ↑mn : ℤ) : ℚ) / ↑Q : ℚ)`, in the form the
`*_dyadic_bound` lemmas carry. -/
meta def mkSignedDyadic (mp mn Q : ℕ) : MetaM Expr := do
  let int := mkConst ``Int
  let rat := mkConst ``Rat
  let mpZ := mkApp3 (mkConst ``Nat.cast [.zero]) int (mkConst ``instNatCastInt) (natLitShared mp)
  let mnZ := mkApp3 (mkConst ``Nat.cast [.zero]) int (mkConst ``instNatCastInt) (natLitShared mn)
  let diff := mkApp6 (mkConst ``HSub.hSub [.zero, .zero, .zero]) int int int
    (mkApp2 (mkConst ``instHSub [.zero]) int (mkConst ``Int.instSub)) mpZ mnZ
  let num := mkApp3 (mkConst ``Int.cast [.zero]) rat (mkConst ``Rat.instIntCast) diff
  let den := mkApp3 (mkConst ``Nat.cast [.zero]) rat (mkConst ``Rat.instNatCast) (natLitShared Q)
  return mkApp6 (mkConst ``HDiv.hDiv [.zero, .zero, .zero]) rat rat rat
    (mkApp2 (mkConst ``instHDiv [.zero]) rat (mkConst ``Rat.instDiv)) num den

/-- The dyadic rational `(↑p / ↑Q : ℚ)` with both casts from `ℕ`. -/
meta def mkNatDyadic (p Q : ℕ) : MetaM Expr := do
  let rat := mkConst ``Rat
  let n := mkApp3 (mkConst ``Nat.cast [.zero]) rat (mkConst ``Rat.instNatCast) (natLitShared p)
  let d := mkApp3 (mkConst ``Nat.cast [.zero]) rat (mkConst ``Rat.instNatCast) (natLitShared Q)
  return mkApp6 (mkConst ``HDiv.hDiv [.zero, .zero, .zero]) rat rat rat
    (mkApp2 (mkConst ``instHDiv [.zero]) rat (mkConst ``Rat.instDiv)) n d

/-- A proof of `|X − q| ≤ eps` from `cert : Real.IsNear X cneg cn cd rn rd`, or an error (raised
in `MetaM`, not the kernel) when the enclosure does not verify the bound. -/
meta def mkVerifyLe (tac : Name) (X q eps cert : Expr) (cneg : Bool) (cn cd rn rd :
      ℕ) : MetaM Expr := do
  let (qneg, qn, qd, qpf) ← recognizeRat q
  let (eneg, en, ed, epf) ← recognizeRat eps
  if eneg then throwError "{tac}: the bound must be positive"
  if cd == 0 || rd == 0 || qd == 0 || ed == 0 then throwError "{tac}: zero denominator"
  -- fast path: when the goal's `q` equals the enclosure centre as a rational (compared by
  -- cross-multiplication, since `q` may be gcd-reduced), `|X − q| = |X − centre| ≤ rn/rd`, so the
  -- bound reduces to `qn·cd = cn·qd` and `rn·ed ≤ en·rd` (`isNear_verify_le_center`).
  if qneg == cneg && qn * cd == cn * qd && rn * ed ≤ en * rd then
    return mkAppN (mkConst ``isNear_verify_le_center)
      #[X, q, eps, toExpr cneg, natLitShared cn, natLitShared cd, natLitShared rn, natLitShared rd,
        natLitShared qn, natLitShared qd, natLitShared en, natLitShared ed, cert, qpf, epf,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  let cp := if cneg then 0 else cn
  let cm := if cneg then cn else 0
  let qp := if qneg then 0 else qn
  let qm := if qneg then qn else 0
  unless qp * (ed * cd * rd) + cm * (qd * ed * rd) + rn * (cd * qd * ed)
      ≤ cp * (qd * ed * rd) + qm * (ed * cd * rd) + en * (qd * cd * rd) do
    throwError "{tac}: the certificate does not verify the stated bound (lower side)"
  unless cp * (qd * ed * rd) + qm * (ed * cd * rd) + rn * (cd * qd * ed)
      ≤ qp * (ed * cd * rd) + cm * (qd * ed * rd) + en * (qd * cd * rd) do
    throwError "{tac}: the certificate does not verify the stated bound (upper side)"
  return mkAppN (mkConst ``isNear_verify_le)
    #[X, q, eps, toExpr cneg, toExpr qneg, natLitShared cn, natLitShared cd, natLitShared rn,
      natLitShared rd,
      natLitShared qn, natLitShared qd, natLitShared en, natLitShared ed, cert, qpf, epf,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]

/-! ### Precision weakening for cached tier constants -/

/-- The centre fields `mkWeakenedNear` emits for radius `1/E`: `cn/cd` floored onto the dyadic
grid `2^⌈log₂(2E)⌉` and `gcd`-reduced. -/
meta def weakenFields (cn cd E : ℕ) : ℕ × ℕ :=
  let B := 2 ^ Nat.clog 2 (2 * E)
  let cnF := cn * B / cd
  let g := gcdPow2 cnF B
  (cnF / g, B / g)

/-- `(proof, cn', cd')` with `proof` a `Real.IsNear x neg cn' cd' 1 E` obtained from the named
`IsNear` constant by one `Real.IsNear.recentre`, centre fields from `weakenFields`. Errors when
the radius `1/E` is too tight. -/
meta def mkWeakenedNear (constName : Name) (x : Expr) (neg : Bool) (cn cd rn rd E : ℕ) :
    MetaM (Expr × ℕ × ℕ) := do
  let (cn', cd') := weakenFields cn cd E
  unless (rn * (cd * cd') + (cn * cd' - cn' * cd) * rd) * E ≤ rd * (cd * cd') do
    throwError "mkWeakenedNear: target radius 1/{E} too tight for {constName}"
  let tier := mkConst constName
  let proof := mkAppN (mkConst ``Real.IsNear.recentre)
    #[x, toExpr neg, natLitShared cn, natLitShared cd, natLitShared rn, natLitShared rd,
      natLitShared cn', natLitShared cd', natLitShared 1, natLitShared E,
      tier, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (proof, cn', cd')

/-- A named tier of the constant `x` for precision `1/E`: `(Euse, cn, cd, proof)` with
`proof : Real.IsNear x false cn cd 1 Euse` from the `10¹⁵` tier `name15` or the `10⁵⁰` tier
`name50` (fields from `val`), recentred to radius `1/(4E)` when `weaken` and the tier is at least
three bits finer than `E`; `none` when `E > 10⁵⁰`. -/
meta def mkConstTier? (x : Expr) (name15 name50 : Name) (val : ℕ → MetaM (ℕ × ℕ)) (E : ℕ)
    (weaken : Bool := false) : MetaM (Option (ℕ × ℕ × ℕ × Expr)) := do
  let some (T, name) :=
      if E ≤ 10 ^ 15 then some (10 ^ 15, name15)
      else if E ≤ 10 ^ 50 then some (10 ^ 50, name50)
      else none
    | return none
  let (pt, Qt) ← val T
  if weaken && 8 * E ≤ T then
    let (proof, cn, cd) ← mkWeakenedNear name x false pt Qt 1 T (4 * E)
    return some (4 * E, cn, cd, proof)
  else
    return some (T, pt, Qt, mkConst name)

/-- The value of `binarySplit Pf Qf m n`. -/
partial def evalFoldGen (Pf Qf : ℕ → ℕ) (m n : ℕ) : ℕ × ℕ × ℕ :=
  if m + 1 == n then (Pf m, Qf m, Pf m)
  else if m < n then
    let k := (m + n) / 2
    let (tl, ql, pl) := evalFoldGen Pf Qf m k
    let (tr, qr, pr) := evalFoldGen Pf Qf k n
    (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)

/-! ### Proof-emitting metaprogram: literals computed in `MetaM`, discharged by `beq` reflection. -/

/-- Widest collapsed base case `proveBS` emits in one application. A lemma
`binarySplit_of_base⟨w⟩` must exist in `Basic.lean` for every width `2 ≤ w ≤ bsBaseCap`. -/
meta def bsBaseCap : ℕ := 16

/-- The collapsed base-case lemma names, indexed by width `n - m` (index 0 unused). -/
meta def baseLemmaName : Array Name :=
  #[.anonymous, ``binarySplit_of_base, ``binarySplit_of_base2, ``binarySplit_of_base3,
    ``binarySplit_of_base4, ``binarySplit_of_base5, ``binarySplit_of_base6,
    ``binarySplit_of_base7, ``binarySplit_of_base8, ``binarySplit_of_base9,
    ``binarySplit_of_base10, ``binarySplit_of_base11, ``binarySplit_of_base12,
    ``binarySplit_of_base13, ``binarySplit_of_base14, ``binarySplit_of_base15,
    ``binarySplit_of_base16]

open Lean Elab Meta in
/-- `evalFoldGen` for monadic value closures. -/
meta partial def evalFoldM (Pf Qf : ℕ → MetaM ℕ) (m n : ℕ) : MetaM (ℕ × ℕ × ℕ) := do
  if m + 1 == n then
    let pm ← Pf m
    return (pm, ← Qf m, pm)
  else if m < n then
    let k := (m + n) / 2
    let (tl, ql, pl) ← evalFoldM Pf Qf m k
    let (tr, qr, pr) ← evalFoldM Pf Qf k n
    return (tl * qr + pl * tr, ql * qr, pl * pr)
  else
    return (0, 1, 1)

open Lean Elab Meta in
/-- `((T, Q, P), proof)` with `proof : binarySplit pE qE mE nE = (T, Q, P)`, the literals computed
from the closures `Pf`/`Qf`; `pE`/`qE` only appear in the proof term and are never reduced. -/
meta partial def proveBS (Pf Qf : ℕ → MetaM ℕ) (pE qE mE nE : Expr) (m n : ℕ) :
    MetaM ((ℕ × ℕ × ℕ) × Expr) := do
  if m < n && n - m ≤ bsBaseCap then
    let (T, Q, P) ← evalFoldM Pf Qf m n
    let pf := mkAppN (.const baseLemmaName[n - m]! [])
      #[mE, nE, reflBoolTrue, qE, natLitShared Q, reflBoolTrue, natLitShared P, pE, reflBoolTrue,
        natLitShared T, reflBoolTrue]
    return ((T, Q, P), pf)
  else if m < n then
    let k := (m + n) / 2
    let kE := natLitShared k
    let ((tl, ql, pl), pfL) ← proveBS Pf Qf pE qE mE kE m k
    let ((tr, qr, pr), pfR) ← proveBS Pf Qf pE qE kE nE k n
    let T := tl * qr + pl * tr
    let Q := ql * qr
    let P := pl * pr
    let pf := mkAppN (.const ``binarySplit_rec [])
      #[pE, qE, mE, nE, kE, natLitShared tl, natLitShared ql, natLitShared pl, natLitShared tr,
        natLitShared qr,
        natLitShared pr, natLitShared T, natLitShared Q, natLitShared P,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, pfL, pfR]
    return ((T, Q, P), pf)
  else
    let pf := mkAppN (.const ``binarySplit_of_le []) #[pE, qE, mE, nE, reflBoolTrue]
    return ((0, 1, 1), pf)

/-- The binder order of `cos_dyadic_bound_f` and `sin_dyadic_bound_f`, as positions in the argument
list `mkEvenOddCertCore` assembles (least-changing arguments first, for olean prefix sharing). -/
meta def trigBoundOrder : Array ℕ :=
  #[1, 18, 4, 5, 17, 26, 2, 19, 3, 20, 7, 15, 10, 16, 6, 8, 9, 11, 0, 13, 14, 23, 12, 24, 25, 21,
    22]

open Lean Elab Meta in
/-- `(proof, neg, cn, Q)` for the `sin`/`cos`/`arctan` even/odd series: two binary splits over
`[0, M-1)`, recombined by `numden` and floor-rounded to `±cn/Q` with `Q = dyadicDenom D`, applied
to `boundLemmaPos` or `boundLemmaNeg` with `nPre` leading `reflBoolTrue` conditions. -/
meta def mkEvenOddCertCore (evenP evenQ oddP oddQ : Name) (fPe fQe fPo fQo : ℕ → ℕ)
    (u v M D : ℕ) (numden : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ)
    (boundLemmaPos boundLemmaNeg : Name) (nPre : ℕ) :
    MetaM (Expr × Bool × ℕ × ℕ) := do
  let Q := dyadicDenom D
  let peE := mkApp (mkConst evenP) (natLitShared u)
  let qeE := mkApp (mkConst evenQ) (natLitShared v)
  let poE := mkApp (mkConst oddP) (natLitShared u)
  let qoE := mkApp (mkConst oddQ) (natLitShared v)
  let ((Te, Qe, Pe), heven) ← proveBS (fun i ↦ pure (fPe i)) (fun i ↦ pure (fQe i))
    peE qeE (natLitShared 0) (natLitShared (M - 1)) 0 (M - 1)
  let ((To, Qo, Po), hodd) ← proveBS (fun i ↦ pure (fPo i)) (fun i ↦ pure (fQo i))
    poE qoE (natLitShared 0) (natLitShared (M - 1)) 0 (M - 1)
  let (Ne, De, No, Do) := numden (Te, Qe, To, Qo)
  let mInt : Int := Int.fdiv (((Ne : Int) * Do - (No : Int) * De) * (Q : Int)) ((De : Int) * Do)
  let neg := decide (mInt < 0)
  let cn := mInt.natAbs
  let args : Array Expr :=
    (#[natLitShared u, natLitShared v, natLitShared M, natLitShared (M - 1), natLitShared Q,
       natLitShared D,
      natLitShared Te, natLitShared Qe,
      natLitShared Pe, natLitShared To, natLitShared Qo, natLitShared Po, natLitShared cn]
      ++ (List.replicate nPre reflBoolTrue).toArray ++ #[heven, hodd]
      ++ #[reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue])
  let thm := if neg then boundLemmaNeg else boundLemmaPos
  let app := mkAppN (mkConst thm)
    (if !neg && nPre == 8 then trigBoundOrder.map (args[·]!) else args)
  return (app, neg, cn, Q)

end BSN
