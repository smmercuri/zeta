module

public import Enclosure.BinarySplit.Functions.Sin
public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Enclosure.BinarySplit.Tactic.Engine
public meta import Enclosure.BinarySplit.Functions.Sin

/-!
# `sin` certificate builders

The metaprogram side of `Functions.Sin`: term-count search, the even/odd certificate builders,
and the π-free triple-angle reduction driver.
-/
@[expose] public section


namespace BSN
open Enclosure

/-- Least `M` satisfying the sin tail guard at `k = 4M+1`: the shared `trigTermCountAux`
seeded at `k = 1`. -/
private meta def sinTermCount (u v D : ℕ) : ℕ := trigTermCountAux u v 0 1 (u * (2 * D)) v

open Lean Elab Term Meta in
/-- Core for `sin (u/v)` at `1/D`: pick `Q = 2^k` and `M`, run the even/odd binary splits over
`[0, M-1)`, and floor-round `Ne/De − No/Do` (the signed value) to `(mp−mn)/Q`. -/
meta def sinCore (u v D : ℕ) : MetaM (Int × ℕ × ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := do
  let Q := dyadicDenom D
  let M := sinTermCount u v D
  let evenQ : ℕ → ℕ := fun k => v ^ 4 * ((4 * k + 2) * (4 * k + 3) * (4 * k + 4) * (4 * k + 5))
  let oddQ : ℕ → ℕ := fun k => v ^ 4 * ((4 * k + 4) * (4 * k + 5) * (4 * k + 6) * (4 * k + 7))
  let (Te, Qe, Pe) := evalFoldGen (fun _ => u ^ 4) evenQ 0 (M - 1)
  let (To, Qo, Po) := evalFoldGen (fun _ => u ^ 4) oddQ 0 (M - 1)
  let Ne : ℕ := u * (Qe + Te); let De : ℕ := v * Qe
  let No : ℕ := u ^ 3 * (Qo + To); let Do : ℕ := 6 * v ^ 3 * Qo
  let s : Int := (Ne : Int) * Do - (No : Int) * De
  let m : Int := Int.fdiv (s * (Q : Int)) ((De : Int) * Do)
  return (m, Q, M, (Te, Qe, Pe), (To, Qo, Po))

open Lean Elab Term Meta in
/-- Build the sin inner enclosure `Real.IsNear (sin (↑u/↑v)) neg cn Q 1 D`; return
`(proof, neg, cn, Q)` with the sign decided in `MetaM` from the signed rounding. A thin wrapper
over the shared `mkEvenOddCertCore` (even value `u(Qe+Te)/(v·Qe)`, odd `u³(Qo+To)/(6v³·Qo)`,
8 leading side conditions of the sign-specialized `sin_dyadic_bound_f`/`_t`). -/
meta def mkSinPos (u v D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  -- `max 1` keeps `M ≥ 1` (needed for `sin_dyadic_bound`'s `hM`); only affects `u = 0`, where
  -- `sinTermCount` returns `0`. Every convergence/tail guard is monotone in `M`, so `M = 1` is
  -- safe.
  let M := max 1 (sinTermCount u v D)
  mkEvenOddCertCore ``sinEvenP ``sinEvenQ ``sinOddP ``sinOddQ
    (sinEvenP u) (sinEvenQ v) (sinOddP u) (sinOddQ v) u v M D
    (fun (Te, Qe, To, Qo) => (u * (Qe + Te), v * Qe, u ^ 3 * (Qo + To), 6 * v ^ 3 * Qo))
    ``sin_dyadic_bound_f ``sin_dyadic_bound_t 8

/-! ### Recursive π-free reduction driver -/

/-- Smallest `k ≥ 1` with `b·3ᵏ > a`, so the reduced argument `θ = a/(b·3ᵏ) < 1`. -/
private meta partial def findTripleK (a b k : ℕ) : ℕ :=
  if b * 3 ^ k > a then k else findTripleK a b (k + 1)

open Lean Elab Term Meta in
/-- Plan the π-free triple-angle reduction of `sin (a/b)` to `1/D`. Returns
`(k, dk, Dk, steps, fneg, fcn, fQ)`: the depth `k`, the inner denominator `dk = b·3ᵏ`, the inner
precision `Dk`, the per-step data `steps` (output denom `dj`, input denom `dj1 = 3·dj`, the
old/new signed centres, input/output precisions `Din`/`Dout`), and the final signed centre
`(fneg,fcn,fQ)`. -/
meta def sinTripleData (a b D : ℕ) :
    MetaM (ℕ × ℕ × ℕ ×
      Array (ℕ × ℕ × Bool × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ) × Bool × ℕ × ℕ) := do
  let k := findTripleK a b 1
  let dk := b * 3 ^ k
  -- forward precision recurrence
  let mut Darr : Array ℕ := #[D]
  let mut Qarr : Array ℕ := #[]
  for _ in [0:k] do
    let Dj := Darr.back!
    let Qj := dyadicDenom (16 * Dj)
    let Dnext := (15 * Dj * Qj + (Qj - Dj) - 1) / (Qj - Dj)
    Darr := Darr.push Dnext
    Qarr := Qarr.push Qj
  let Dk := Darr[k]!
  -- inner signed centre for sin(a/dk)
  let (sInt, Qinner, _, _, _) ← sinCore a dk Dk
  let mut steps : Array (ℕ × ℕ × Bool × ℕ × ℕ × Bool × ℕ × ℕ × ℕ × ℕ) := #[]
  let mut s : Int := sInt
  let mut Qprev : ℕ := Qinner
  for i in [0:k] do
    let j := k - 1 - i
    let dj := b * 3 ^ j
    let dj1 := b * 3 ^ (j + 1)
    let QN := Qarr[j]!
    let M : Int := 3 * s * (Qprev : Int) ^ 2 - 4 * s ^ 3
    let sN : Int := Int.fdiv (M * (QN : Int)) ((Qprev : Int) ^ 3)
    steps := steps.push (dj, dj1, decide (s < 0), s.natAbs, Qprev, decide (sN < 0), sN.natAbs, QN,
      Darr[j + 1]!, Darr[j]!)
    s := sN
    Qprev := QN
  return (k, dk, Dk, steps, decide (s < 0), s.natAbs, Qprev)

open Lean Elab Term Meta in
/-- Build the *positive-argument* triple-angle (large-argument) core enclosure
`Real.IsNear (sin (↑a/↑b)) fneg fcn fQ 1 D`, returning `(proof, fneg, fcn, fQ)`. The
positive-core analogue of `mkSinPos` for large arguments. -/
meta def mkSinTriplePos (a b D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  let (k, dk, Dk, steps, fneg, fcn, fQ) ← sinTripleData a b D
  if k == 0 then throwError "sin_triple: argument already small"
  let (innerPf, _, _, _) ← mkSinPos a dk Dk
  let refls : Array Expr := (List.replicate 11 reflBoolTrue).toArray
  let mut pf := innerPf
  for st in steps do
    let (dj, dj1, negO, cO, QO, negN, cN, QN, Din, Dout) := st
    pf := mkAppN (mkConst ``sin_triple_step_arg)
      (#[natLitShared a, natLitShared dj, natLitShared dj1, toExpr negO, natLitShared cO,
         natLitShared QO,
        toExpr negN, natLitShared cN, natLitShared QN, natLitShared Din, natLitShared Dout]
          ++ refls ++ #[pf])
  return (pf, fneg, fcn, fQ)

end BSN
