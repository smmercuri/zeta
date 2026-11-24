/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.BinarySplit.Tactic.Exp
public import Enclosure.BinarySplit.Tactic.Sin
public import Enclosure.BinarySplit.Tactic.Cos
public import Enclosure.BinarySplit.Tactic.Pi
public import Enclosure.BinarySplit.Tactic.Log2
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Range-reduction certificate builders for `sin` and `cos`

The metaprogram side of `Reduce.Sin`: builders that reduce a large argument mod `π/2` and certify
the reduced-argument enclosure at the rational centre.
-/
@[expose] public section


namespace BSN
open Enclosure

-- Inside `BSN` a bare `open Real` would resolve to `BSN.Real` (home of `Real.IsNear`),
-- so open the root namespace explicitly for `π` and the trigonometric lemmas.
open _root_.Real

open Lean Elab Term Meta

/-- The `forCos`-independent part of the range reduction of `a/b` at precision `1/D`:
`(#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE, rcvE, hrc])`, with the quadrant
`k = ⌊(a/b)/(π/2)⌋ = 4·qq + j`, `piPf` enclosing `π` as `Pc/Q` at precision `1/E`, the reduced
argument `rcvE = u/v`, `xE = a/b`, and the centre identity `hrc`. -/
meta def mkTrigReduce (a b D : ℕ) : MetaM (Array Nat × Array Expr) := do
  let (Pc0, Q0) ← piVal (10 * (a / b + 1) + 100)
  let den := b * Pc0
  let kRaw := (2 * a * Q0) / den
  if kRaw == 0 then throwError "mkTrigPosReduced: argument already in range"
  -- The cheap `π` can only push the floor one too high when `2a·Q₀/den` sits just above an
  -- integer, so a remainder above a sixteenth of `den` settles `k` without the precise `π`.
  -- Its error is `~kRaw/(π·E₀)` with `E₀ ≥ 10a/b`, far inside that margin.
  let k ←
    if 16 * ((2 * a * Q0) % den) > den then
      pure kRaw
    else do
      let (Pc0', Q0') ← piVal (kRaw * D)
      pure (if 2 * a * Q0' < kRaw * (b * Pc0') then kRaw - 1 else kRaw)
  if k == 0 then throwError "mkTrigPosReduced: argument already in range"
  let Eneed := k * D
  let (E, Pc, Q, piPf?) ← do
    match ← mkPiTier? Eneed with
    | some (Euse, Pc, Q, pf) => pure (Euse, Pc, Q, some pf)
    | none => do let (Pc, Q) ← piVal Eneed; pure (Eneed, Pc, Q, none)
  let lhs := 2 * a * Q
  let rhs := k * (b * Pc)
  if lhs < rhs then throwError "mkTrigPosReduced: negative reduced centre (pathological x)"
  let u := lhs - rhs
  let v := 2 * (b * Q)
  let qq := k / 4
  let j := k % 4
  let piPf ← match piPf? with
    | some pf => pure pf
    | none => do let (_, _, pf) ← mkPiProof E; pure pf
  let xE := mkCastDivR a b
  let rcvE := mkCastDivR u v
  -- One centre identity per quadrant, each stating the multiplier as `4·qq + j` for its own `j`,
  -- the shape the quadrant lemma's `hrc` binder carries.
  let argLemma := #[``sin_reduce_arg_pos_rat_q0, ``sin_reduce_arg_pos_rat_q1,
    ``sin_reduce_arg_pos_rat_q2, ``sin_reduce_arg_pos_rat_q3][j]!
  let hrc := mkAppN (Lean.mkConst argLemma)
    #[natLitShared a, natLitShared b, natLitShared Pc, natLitShared Q, natLitShared qq,
      natLitShared u, natLitShared v,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE, rcvE, hrc])

/-- `(proof, neg, cn, Q)` enclosing `cos (a/b)` (if `forCos`) or `sin (a/b)` to radius `1/D` by
range reduction, the reduction memoized in `trigReduceCache`. -/
meta def mkTrigPosReduced (forCos : Bool) (a b D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ) := do
  let red ← match ← trigReduceCache.get with
    | some (key, r) =>
        if key == (a, b, D) then pure r
        else do let r ← mkTrigReduce a b D; trigReduceCache.set (some ((a, b, D), r)); pure r
    | none => do let r ← mkTrigReduce a b D; trigReduceCache.set (some ((a, b, D), r)); pure r
  let (nats, exprs) := red
  let qq := nats[1]!; let j := nats[2]!; let E := nats[3]!
  let Pc := nats[4]!; let Q := nats[5]!; let u := nats[6]!; let v := nats[7]!
  let piPf := exprs[0]!; let xE := exprs[1]!; let rcvE := exprs[2]!; let hrc := exprs[3]!
  let Dp := 2 * D
  let innerIsCos := if forCos then (j == 0 || j == 2) else (j == 1 || j == 3)
  -- The reduction's argument denominator carries the precision of the `π` constant it used, which
  -- the series then raises to a power. When `v` exceeds `vr = 2^vb ≈ 2^12·Dp`, round the argument
  -- onto `·/vr` and evaluate the series there; `cos_arg_round`/`sin_arg_round` add the rounding
  -- error to the radius, and the inner precision `Din` exceeds `Dp` by about a thousandth to
  -- cover it.
  let vb := Nat.clog 2 Dp + 12
  let vr : ℕ := 2 ^ vb
  let Din := Dp + Dp / 1024 + 1
  let (hinner, ineg, icn, Qd) ←
    if vr < v then do
      let ur : ℕ := u * vr / v
      let (hin, ineg, icn, Qd) ← if innerIsCos then mkCosPos ur vr Din else mkSinPos ur vr Din
      let roundName := if innerIsCos then ``cos_arg_round else ``sin_arg_round
      let pf := mkAppN (Lean.mkConst roundName)
        #[toExpr ineg, natLitShared icn, natLitShared Qd,
          natLitShared u, natLitShared v, natLitShared ur, natLitShared vr,
          natLitShared Din, natLitShared Dp, hin, reflBoolTrue]
      pure (pf, ineg, icn, Qd)
    else
      if innerIsCos then mkCosPos u v Dp else mkSinPos u v Dp
  let quadName := if forCos then #[``cos_reduce0, ``cos_reduce1, ``cos_reduce2, ``cos_reduce3][j]!
    else #[``sin_reduce0, ``sin_reduce1, ``sin_reduce2, ``sin_reduce3][j]!
  let flips := if forCos then (j == 1 || j == 2) else (j == 2 || j == 3)
  let cert :=
      mkAppN (Lean.mkConst quadName) #[xE, rcvE, natLitShared Pc, natLitShared Q, toExpr ineg,
    natLitShared icn, natLitShared Qd, natLitShared qq, natLitShared E, natLitShared Dp,
    natLitShared D, hrc, piPf, hinner, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (cert, if flips then !ineg else ineg, icn, Qd)

end BSN
