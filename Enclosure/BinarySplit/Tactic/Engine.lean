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

/-- Memo cache for `piVal` (used in `Tactic.Pi`): `π` is a constant, so `(P, Q)` at a given
precision `E` is computed once per process. The range reduction requests `piVal` repeatedly (three
per trig reduction, for the cos and sin of every head-sum term) at a handful of distinct precisions,
so the cache collapses those requests to one Machin arctan binary split per precision. Lives here
(not in `Tactic.Pi`) so it is initialized before `Tactic.Pi`'s own `pi_near_*` constants elaborate
against `piVal`. -/
initialize piValCache : IO.Ref (Std.HashMap Nat (Nat × Nat)) ← IO.mkRef ∅

/-- Memo caches for the `n`-only leaf enclosures `√(N/M)` and `log(a/b)`, which the zeta head sum
rebuilds for the same `n` at the same precision on every bracket endpoint of a chunk. The value
is the raw `RNear` payload `(proof, neg, cn, cd, rn, rd)` (kept tuple-form here so this module need
not depend on `RNear`, defined downstream in `Tactic.Enclosures`); the enclosure proof is a closed
term about `√(N/M)` / `log(a/b)`, so it is reused verbatim. Living here (imported) means they are
initialized before `Tactic.Enclosures`' own `sqrt_near%`/`log_near%` benchmark defs elaborate. -/
initialize sqrtNearCache : IO.Ref (Std.HashMap (Nat × Nat × Nat)
      (Lean.Expr × Lean.Expr × Bool × Nat × Nat × Nat × Nat)) ← IO.mkRef ∅
initialize logNearCache : IO.Ref (Std.HashMap (Nat × Nat × Nat × Nat)
      (Lean.Expr × Lean.Expr × Bool × Nat × Nat × Nat × Nat)) ← IO.mkRef ∅

/-- Memo for the `forCos`-independent part of the `sin`/`cos` range reduction, holding the argument
`(a, b, D)` it was computed at. `cos(t·log n)` and `sin(t·log n)` reduce the *same* argument and
differ only in the inner Taylor series and quadrant lemma, and they are built one after the other,
so a single slot catches every reuse there is. Value `(#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE,
rcvE, hrc])`, packed as arrays so this module need not depend on a `Reduce` structure.

One slot rather than a table because the arguments are phases, all distinct: a table holds thousands
of entries keyed on pairs of big integers to serve the one repeat, and hashing those keys costs more
than recomputing the reduction would. -/
initialize trigReduceCache : IO.Ref (Option ((Nat × Nat × Nat) × (Array Nat × Array Lean.Expr))) ←
  IO.mkRef none

/-! ### Proof-emitting metaprogram (literals computed in `MetaM`, `beq` reflection) -/

open Lean Elab Meta Tactic

/-! ### Shared real-value `Expr` builders

The enclosed real of a leaf/combinator is a fixed function of its inputs, built directly (matching
the certificate lemmas' conclusions) rather than read back from a proof's type by `inferType`.
These primitives live here so the `log2`/`π` factor lifts (`mkBoundAux`) can state their aux-lemma
types too. -/

/-- The type `ℝ`. -/
meta def realTyE : Expr := mkConst ``Real

/-- `(↑n : ℝ)` (`@Nat.cast ℝ Real.instNatCast n`). -/
meta def mkNatCastR (n : ℕ) : Expr :=
  mkApp2 (mkConst ``Nat.cast [.zero]) realTyE (mkConst ``Real.instNatCast) |>.app (natLitShared n)

/-- `(↑u / ↑v : ℝ)`, the argument form the trig/exp/log certificate lemmas conclude about
(`Real.sin ((u:ℝ)/v)` etc.), matching `@HDiv.hDiv ℝ ℝ ℝ (instHDiv (DivInvMonoid.toDiv
Real.instDivInvMonoid)) ↑u ↑v`. -/
meta def mkCastDivR (u v : ℕ) : Expr :=
  mkAppN (mkConst ``HDiv.hDiv [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHDiv [.zero]) realTyE
        (mkApp2 (mkConst ``DivInvMonoid.toDiv [.zero]) realTyE (mkConst ``Real.instDivInvMonoid)),
      mkNatCastR u, mkNatCastR v]

/-- `-x` on `ℝ` (`@Neg.neg ℝ Real.instNeg x`). -/
meta def mkNegR (x : Expr) : Expr :=
  mkApp3 (mkConst ``Neg.neg [.zero]) realTyE (mkConst ``Real.instNeg) x

/-- `((-↑u) / ↑v : ℝ)`, the RHS of `sfrac_true_div` (`Real.sin ((-(u:ℝ))/v)` etc.), matching
`HDiv.hDiv ℝ ℝ ℝ … (Neg.neg ↑u) ↑v`. -/
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

/-- `Real.f x` for a unary real function `f` (`Real.exp`/`Real.sin`/`Real.cos`/`Real.log`/
`Real.sqrt`/`Real.arctan`), applied to the enclosed real `x`. -/
meta def mkRealFn (fn : Name) (x : Expr) : Expr := mkApp (mkConst fn) x

/-- The `ℕ` numeral `(n : ℕ)` in `OfNat.ofNat ℕ n (instOfNatNat n)` form. -/
private meta def mkNatOfNat (n : ℕ) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) (mkConst ``Nat) (mkRawNatLit n)
    (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

/-- The `ℝ` numeral literal `(2 : ℝ)` in the elaborated `OfNat.ofNat ℝ 2 (instOfNatAtLeastTwo …)`
form, matching the `Real.log 2` argument the shared `log2` tier constants conclude about. -/
meta def mkRealTwo : Expr :=
  let atLeastTwo := mkApp2 (mkConst ``Nat.instAtLeastTwoHAddOfNat)
    (mkNatOfNat 1) (mkApp (mkConst ``Nat.instNeZeroSucc) (mkNatOfNat 0))
  mkApp3 (mkConst ``OfNat.ofNat [.zero]) realTyE (mkRawNatLit 2)
    (mkApp4 (mkConst ``instOfNatAtLeastTwo [.zero]) realTyE (mkRawNatLit 2)
      (mkConst ``Real.instNatCast) atLeastTwo)

/-- `Real.IsNear x neg cn cd rn rd` as an `Expr`, from the enclosed real `x` (built directly) and
the literal fields. -/
meta def mkIsNearTy (x : Expr) (neg : Bool) (cn cd rn rd : ℕ) : Expr :=
  mkAppN (mkConst ``Real.IsNear)
    #[x, toExpr neg, natLitShared cn, natLitShared cd, natLitShared rn, natLitShared rd]

/-- Lift a fully-applied bound proof of the given type `ty` into its own auxiliary lemma and return
a reference to it (`mkConst`), so the enclosing definition body stays a single constant. Shared by
the `log2`/`π` Machin factor proofs. The caller passes `ty` directly (built from the factor's
literal fields), so it is not re-derived from `pf` by `inferType`. Value and type are
`instantiateMVars`'d first (else the kernel rejects the aux lemma with "declaration has
metavariables"). -/
meta def mkBoundAux (ty pf : Expr) : MetaM Expr := do
  let pf ← instantiateMVars pf
  let ty ← instantiateMVars ty
  return mkConst (← mkAuxLemma [] ty pf)

/-- The dyadic denominator for precision `1/D`: the least power of two `≥ 2·D`, so that
the rounding error `1/Q ≤ 1/(2D)`. -/
meta def dyadicDenom (D : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * D)

/-- Primitive-form `ℕ` expression builders (no `HMul`/`HAdd`/`HPow` instance indirection in
kernel-checked positions). -/
meta def natMulE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.mul) a b
meta def natAddE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.add) a b
meta def natSuccE (a : Expr) : Expr := mkApp (mkConst ``Nat.succ) a
meta def natPowE (a b : Expr) : Expr := mkApp2 (mkConst ``Nat.pow) a b
meta def natFactE (a : Expr) : Expr := mkApp (mkConst ``Nat.factorial) a

/-- One-time evaluation lemma `e = <literal>` for a closed `ℕ` expression, `mkAuxLemma`-deduped, so
each distinct value (a factorial, a large power) is computed once per module and later cited. -/
meta def mkNatEvalAux (e : Expr) (v : ℕ) : MetaM Expr := do
  let nm ← mkAuxLemma [] (mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) e (natLitShared v))
    (mkApp2 (Expr.const ``Eq.refl [Level.one]) (mkConst ``Nat) (natLitShared v))
  return mkConst nm

/-- Shared term-count search for the factorial even/odd series (`sin` and `cos`): the least `M`
satisfying the tail guard at index `k`. Carries `L = u^k · 2D` and `R = v^k · k!` as running
products, each updated by one big×small multiply per step, so the guard `u^k·2D ≤ v^k·k!` needs no
big×big products. The wrappers `sinTermCount`/`cosTermCount` differ only in the seeds (`k = 1` for
sin's `4M+1` tail index, `k = 0` for cos's `4M`). -/
partial def trigTermCountAux (u v M k L R : ℕ) : ℕ :=
  if u.blt ((k + 1) * v) && (2 * u ^ 2).ble ((k + 1) ^ 2 * v ^ 2)
      && (2 * L).ble R then M
  else trigTermCountAux u v (M + 1) (k + 4) (L * u ^ 4)
    (R * (v ^ 4 * ((k + 1) * (k + 2) * (k + 3) * (k + 4))))

/-- The signed dyadic rational `(((↑mp - ↑mn : ℤ) : ℚ) / ↑Q : ℚ)` built directly as an `Expr`. The
signed numerator is a difference of two `ℕ` `mp - mn` (exactly one nonzero), cast `ℕ → ℤ → ℚ`, over
`Q` cast `ℕ → ℚ`: it matches the `ℚ`-cast numerator the `*_dyadic_bound` lemmas carry. -/
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

/-- The dyadic rational `(↑p / ↑Q : ℚ)` built directly as an `Expr` (both `ℕ`-casts).
The `ℕ`-numerator analogue of `mkSignedDyadic` (the `*_dyadic_bound` lemmas carry a
`ℕ`-cast numerator). -/
meta def mkNatDyadic (p Q : ℕ) : MetaM Expr := do
  let rat := mkConst ``Rat
  let n := mkApp3 (mkConst ``Nat.cast [.zero]) rat (mkConst ``Rat.instNatCast) (natLitShared p)
  let d := mkApp3 (mkConst ``Nat.cast [.zero]) rat (mkConst ``Rat.instNatCast) (natLitShared Q)
  return mkApp6 (mkConst ``HDiv.hDiv [.zero, .zero, .zero]) rat rat rat
    (mkApp2 (mkConst ``instHDiv [.zero]) rat (mkConst ``Rat.instDiv)) n d

/-- Close a `|X − q| ≤ eps` goal from an `IsNear` certificate of `X`: the enclosure fields
`(cneg, cn, cd, rn, rd)` are passed directly by the caller (threaded from the certificate builder,
not read off the type), `q` and `eps` are recognised, the two containment conditions are pre-checked
in `MetaM` (so a false or too-tight claim errors in the tactic, not in the kernel), and the
`isNear_verify_le` application is returned. `X` is the goal's own minuend expression; the
certificate's enclosed real must be definitionally equal to it. `cert : Real.IsNear _ cneg cn cd rn
rd`. -/
meta def mkVerifyLe (tac : Name) (X q eps cert : Expr) (cneg : Bool) (cn cd rn rd :
      ℕ) : MetaM Expr := do
  let (qneg, qn, qd, qpf) ← recognizeRat q
  let (eneg, en, ed, epf) ← recognizeRat eps
  if eneg then throwError "{tac}: the bound must be positive"
  if cd == 0 || rd == 0 || qd == 0 || ed == 0 then throwError "{tac}: zero denominator"
  -- fast path: when the goal's `q` equals the enclosure centre as a rational (every `approx%`+
  -- `bound` path, `q` may be gcd-reduced, so compare by cross-multiplication), `|X − q| =
  -- |X − centre| ≤ rn/rd`, so the bound collapses to `qn·cd = cn·qd` (one big multiply) and
  -- `rn·ed ≤ en·rd`, skipping `isNear_verify_le`'s four-denominator triple products (the kernel
  -- bottleneck at high precision).
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

/-- Centre fields for weakening an enclosure to radius `1/E`: floor the centre `cn/cd` onto the
dyadic grid `B = 2^⌈log₂(2E)⌉`, then `gcd`-reduce. Pure, so tier-planning code can predict the
exact fields `mkWeakenedNear` emits. -/
meta def weakenFields (cn cd E : ℕ) : ℕ × ℕ :=
  let B := 2 ^ Nat.clog 2 (2 * E)
  let cnF := cn * B / cd
  let g := Nat.gcd cnF B
  (cnF / g, B / g)

/-- Weaken a named `IsNear` constant (enclosed real `x`, fields `neg cn cd rn rd`) to a coarser
enclosure of radius exactly `1/E`, by one `Real.IsNear.recentre` over `mkConst constName`. The
recentred centre has ~`log₂ E`-bit fields (`weakenFields`). The radius condition `rn/rd ≤ 1/(2E)` is
checked natively, so a too-tight call errors here. Returns `(proof, cn', cd')`; the caller passes
the enclosed real `x` directly (`Real.pi`/`Real.log 2` for the shared tiers) instead of it being
read off the constant's type. -/
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

/-- Generic pure value of `binarySplit Pf Qf m n` (for the function drivers' sub-series). -/
partial def evalFoldGen (Pf Qf : ℕ → ℕ) (m n : ℕ) : ℕ × ℕ × ℕ :=
  if m + 1 == n then (Pf m, Qf m, Pf m)
  else if m < n then
    let k := (m + n) / 2
    let (tl, ql, pl) := evalFoldGen Pf Qf m k
    let (tr, qr, pr) := evalFoldGen Pf Qf k n
    (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)

/-! ### Proof-emitting metaprogram: literals computed in `MetaM`, discharged by `beq` reflection. -/

/-- Widest collapsed base case `proveBS` emits in one application: `binarySplit_of_base⟨w⟩`
must exist for every width `2 ≤ w ≤ bsBaseCap` (width 1 is `binarySplit_of_base`); the ladder
in `Basic.lean` goes up to 16. -/
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
/-- `evalFoldGen` over the monadic value closures: the pure result tuple of `binarySplit p q m n`,
for the collapsed base cases of `proveBS`. -/
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
/-- Build `binarySplit p q mE nE = (literal 3-tuple)` and return `((T,Q,P), proof)`. Leaf values
come from the closures `Pf`/`Qf` (pass the native compiled sequence functions, e.g.
`pure ∘ artanhP u`); `pE`/`qE` are used only inside the emitted proof term, never reduced. -/
meta partial def proveBS (Pf Qf : ℕ → MetaM ℕ) (pE qE mE nE : Expr) (m n : ℕ) :
    MetaM ((ℕ × ℕ × ℕ) × Expr) := do
  if m < n && n - m ≤ bsBaseCap then
    let (T, Q, P) ← evalFoldM Pf Qf m n
    let pf := mkAppN (.const baseLemmaName[n - m]! [])
      #[pE, qE, mE, nE, natLitShared T, natLitShared Q, natLitShared P,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
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

open Lean Elab Meta in
/-- Shared even/odd certificate core for `sin`/`cos`/`arctan`. Runs the two binary splits over
`[0, M-1)` on the sequences named `evenP u`/`evenQ v`/`oddP u`/`oddQ v` (values from the pure
closures `fPe`/`fQe`/`fPo`/`fQo`), recombines the sub-series values `Ne/De − No/Do` (via the
per-function closure `numden`), floor-rounds the signed value to `(neg, cn)` over
`Q = dyadicDenom D`, and assigns the sign-specialized bound lemma (`boundLemmaPos`/`boundLemmaNeg`)
with the split bound `Mm = M − 1`, `nPre` leading `reflBoolTrue` conditions (8 for `sin`/`cos`, 7
for `arctan`), the two split certificates, and the 4 trailing rounding/precision conditions (the
tail guard's factor is expressed via the split's own denominator, so the kernel never reduces a
factorial). Returns `(proof, neg, cn, Q)`. -/
meta def mkEvenOddCertCore (evenP evenQ oddP oddQ : Name) (fPe fQe fPo fQo : ℕ → ℕ)
    (u v M D : ℕ) (numden : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ)
    (boundLemmaPos boundLemmaNeg : Name) (nPre : ℕ) :
    MetaM (Expr × Bool × ℕ × ℕ) := do
  let Q := dyadicDenom D
  let peE := mkApp (mkConst evenP) (natLitShared u)
  let qeE := mkApp (mkConst evenQ) (natLitShared v)
  let poE := mkApp (mkConst oddP) (natLitShared u)
  let qoE := mkApp (mkConst oddQ) (natLitShared v)
  let ((Te, Qe, Pe), heven) ← proveBS (fun i => pure (fPe i)) (fun i => pure (fQe i))
    peE qeE (natLitShared 0) (natLitShared (M - 1)) 0 (M - 1)
  let ((To, Qo, Po), hodd) ← proveBS (fun i => pure (fPo i)) (fun i => pure (fQo i))
    poE qoE (natLitShared 0) (natLitShared (M - 1)) 0 (M - 1)
  let (Ne, De, No, Do) := numden (Te, Qe, To, Qo)
  let mInt : Int := Int.fdiv (((Ne : Int) * Do - (No : Int) * De) * (Q : Int)) ((De : Int) * Do)
  let neg := decide (mInt < 0)
  let cn := mInt.natAbs
  let app := mkAppN (mkConst (if neg then boundLemmaNeg else boundLemmaPos))
    (#[natLitShared u, natLitShared v, natLitShared M, natLitShared (M - 1), natLitShared Q,
       natLitShared D,
      natLitShared Te, natLitShared Qe,
      natLitShared Pe, natLitShared To, natLitShared Qo, natLitShared Po, natLitShared cn]
      ++ (List.replicate nPre reflBoolTrue).toArray ++ #[heven, hodd]
      ++ #[reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue])
  return (app, neg, cn, Q)

end BSN
