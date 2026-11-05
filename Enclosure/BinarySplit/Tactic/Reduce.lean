module

public import Enclosure.BinarySplit.Reduce.Sin
public import Enclosure.BinarySplit.Reduce.Exp
public import Enclosure.BinarySplit.Tactic.Exp
public import Enclosure.BinarySplit.Tactic.Sin
public import Enclosure.BinarySplit.Tactic.Cos
public import Enclosure.BinarySplit.Tactic.Pi
public import Enclosure.BinarySplit.Tactic.Log2
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Range-reduction certificate builders for `sin` and `exp`

The metaprogram side of `Reduce.Sin`/`Reduce.Exp`: builders that reduce a large argument
(`sin`/`cos` mod `π/2`, `exp` by `log 2` as `exp X = 2ᵏ·exp r`) and certify the reduced-argument
enclosure at the rational centre.
-/
@[expose] public section


namespace BSN
open Enclosure

-- Inside `BSN` a bare `open Real` would resolve to `BSN.Real` (the `Real.IsNear` layer),
-- so open the root namespace explicitly for `π` and the trigonometric lemmas.
open _root_.Real

/-! ### `sin` range-reduction planning -/

open Lean Elab Term Meta in
/-- Shared planning for `sin X` to precision `1/D` by range reduction. Picks `k = ⌊X/(π/2)⌋` (so the
reduced argument is in `[0, π/2)`), the `π` precision (`Eneed = k·D`, a cached tier via `mkPiTier?`)
and inner precision `Dp = 2D`, the dyadic `π = Pc/PQ`, the in-range numerator `u` with denominator
`v = 2·PQ` (`X − k·(Pr/2) = u/v`), and the in-range signed centre `(ineg, icn, Qd)`. Returns
everything the value elaborator and the tactic need, including the tier `π` proof when one applies
(`none` above the 10⁵⁰ tier). Steps `k` down by one if the cheap-`π` floor overshoots (negative
centre). Errors only if `k = 0` (the argument is already in range). -/
private meta def sinReduceCore (X Dgoal : ℕ) :
    MetaM (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Bool × Bool × ℕ × ℕ × Option Expr) := do
  let Dp := 2 * Dgoal
  -- cheap π to fix `k = ⌊2X·PQ₀/Pc₀⌋`
  let (Pc0, Q0) ← piVal (10 * X + 100)
  let kRaw := (2 * X * Q0) / Pc0
  if kRaw == 0 then throwError "sinReduceCore: argument already in range"
  -- When `X` sits just below a multiple of `π/2`, a cheap-`π` floor can overshoot by one, which
  -- would push the reduced centre `X − k·(Pr/2)` negative. Detect that against a precise `π` and
  -- step `k` down by one: the centre then lands near `π/2`, still in `[0, π/2)`, so the centre
  -- identity and quadrant lemmas apply unchanged (`k − 1` only shifts which quadrant `ε`/`g` is
  -- used).
  let E0 := kRaw * Dgoal
  let (Pc0', Q0') ← piVal E0
  let k := if 2 * X * Q0' < kRaw * Pc0' then kRaw - 1 else kRaw
  if k == 0 then throwError "sinReduceCore: argument already in range"
  -- certificate-precision π: a shared constant (15 dp / 50 dp, kernel-checked once) serves any
  -- `Eneed ≤ 10⁵⁰` (`Eneed = k·Dgoal` is the `htot` requirement) through `mkPiTier?`; otherwise
  -- fall back to the tight per-call precision.
  let Eneed := k * Dgoal
  let (E, Pc, Q, piPf?) ← do
    match ← mkPiTier? Eneed with
    | some (Euse, Pc, Q, pf) => pure (Euse, Pc, Q, some pf)
    | none => do let (Pc, Q) ← piVal Eneed; pure (Eneed, Pc, Q, none)
  let lhs := 2 * X * Q
  let rhs := k * Pc
  if lhs < rhs then
    throwError "sinReduceCore: reduced centre still negative after step-down (pathological X)"
  let u := lhs - rhs
  let v := 2 * Q
  let qq := k / 4
  let j := k % 4
  let isCos := j == 1 || j == 3
  let (m, Qd, _, _, _) ← if isCos then cosCore u v Dp else sinCore u v Dp
  return (j, qq, k, E, Dp, Pc, Q, u, v, isCos, decide (m < 0), m.natAbs, Qd, piPf?)

/-! ### `exp` `log 2` range-reduction planning -/

open Lean Elab Term Meta in
/-- Planning for `exp X` to precision `1/D` by `log 2` reduction. Picks `k = ⌊X/log 2⌋` from a cheap
`log 2`, sets the certificate precisions `Dp = 2^(k+1)·D` and `Eneed = 6k·2ᵏ·D` (making the combine
`2ᵏ·(3k/E + 1/Dp) ≤ 1/D` hold with equality at `E = Eneed`), the certified `log 2 = Lp/LQ` (a cached
tier via `mkLog2Tier?`), the centre numerator `u = X·LQ − k·Lp`, and the inner dyadic
`vp/vQ ≈ exp(u/LQ)`. Steps `k` down by one if the centre would be negative. Returns
`(k, E, Dp, Lp, LQ, u, vp, vQ, pfL?)`, with the tier `log 2` proof when one applies (`none` above
the 10⁵⁰ tier). -/
private meta def expReducePlan (X D : ℕ) :
    MetaM (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Option Expr) := do
  let (Lp0, LQ0) ← log2ValAt (100 * X + 1000)
  let k0 := X * LQ0 / Lp0
  if k0 == 0 then throwError "expReducePlan: argument already small"
  let (Lpa, LQa) ← log2ValAt (6 * k0 * 2 ^ k0 * D)
  let k := if X * LQa < k0 * Lpa then k0 - 1 else k0
  if k == 0 then throwError "expReducePlan: argument already small"
  -- certificate-precision `log 2`: a shared constant (15 dp / 50 dp, kernel-checked once)
  -- serves any `Eneed ≤ 10⁵⁰` (`Eneed = 6k·2ᵏ·D`, the `htot` requirement) through
  -- `mkLog2Tier?`; else build fresh. The need grows like `2ᵏ`, so only small/medium `k`
  -- land on a tier.
  let Eneed := 6 * k * 2 ^ k * D
  let Dp := 2 ^ (k + 1) * D
  let (E, Lp, LQ, pfL?) ← do
    match ← mkLog2Tier? Eneed with
    | some (Euse, Lp, LQ, pf) => pure (Euse, Lp, LQ, some pf)
    | none => do let (Lp, LQ) ← log2ValAt Eneed; pure (Eneed, Lp, LQ, none)
  let u := X * LQ - k * Lp
  let (vp, vQ, _, _) ← expCore u LQ Dp
  return (k, E, Dp, Lp, LQ, u, vp, vQ, pfL?)

open Lean Elab Term Meta in
/-- Build the `log 2` range-reduction certificate for `|Real.exp X − 2ᵏ·(vp/vQ)| ≤ 1/D`
(`X` a large nonnegative integer). -/
meta def mkExpLn2Cert (X D : ℕ) : MetaM (Expr × Bool × ℕ × ℕ × ℕ × ℕ) := do
  let (k, E, Dp, Lp, LQ, u, vp, vQ, pfL?) ← expReducePlan X D
  -- the shared named `log 2` constant from the plan; above the 10⁵⁰ tier build a fresh
  -- certificate at the tight precision `E`.
  let pfL ← match pfL? with
    | some pf => pure pf
    | none => do let (_, _, pf) ← mkLog2Proof E; pure pf
  let (hinner, _, _) ← mkExpPos u LQ Dp
  -- args: 11 literals, then hPf, hL, hlink, hinner, hLQ/hE/hDp/hD, hle1, htot
  let cert := mkAppN (mkConst ``exp_reduce_step)
    #[natLitShared X, natLitShared k, natLitShared E, natLitShared Lp, natLitShared LQ,
      natLitShared Dp, natLitShared D,
      natLitShared u, natLitShared vp, natLitShared vQ, natLitShared (2 ^ k * vp),
      reflBoolTrue, pfL, reflBoolTrue, hinner, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue]
  -- `exp_reduce_step` concludes `Real.IsNear (Real.exp ↑X) false (2^k·vp) vQ 1 D`.
  return (cert, false, 2 ^ k * vp, vQ, 1, D)

open Lean Elab Term Meta

/-- The `forCos`-independent part of the range reduction of `a/b` at precision `1/D`: the quadrant
`k = ⌊(a/b)/(π/2)⌋` (stepped down on cheap-`π` overshoot), the `π` tier, the exact rational centre
`u/v`, and the `Expr`s (`piPf`, `xE`, `rcvE`, `hrc`) shared by the `sin` and `cos` finishes. Returns
`(#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE, rcvE, hrc])`. `mkTrigPosReduced` memoizes this so cos and
sin of the same argument compute it once. -/
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
  let real := Lean.mkConst ``Real
  let natCastR := fun (n : ℕ) =>
    mkApp3 (Lean.mkConst ``Nat.cast [.zero]) real (Lean.mkConst ``Real.instNatCast) (natLitShared n)
  let mkDivR := fun (x y : ℕ) => mkApp6 (Lean.mkConst ``HDiv.hDiv [.zero, .zero, .zero])
    real real real
    (mkApp2 (Lean.mkConst ``instHDiv [.zero]) real
      (mkApp2 (Lean.mkConst ``DivInvMonoid.toDiv [.zero]) real
        (Lean.mkConst ``Real.instDivInvMonoid)))
    (natCastR x) (natCastR y)
  let xE := mkDivR a b
  let rcvE := mkDivR u v
  -- One centre identity per quadrant, each stating the multiplier as `4·qq + j` for its own `j`,
  -- the shape the quadrant lemma's `hrc` binder carries.
  let argLemma := #[``sin_reduce_arg_pos_rat_q0, ``sin_reduce_arg_pos_rat_q1,
    ``sin_reduce_arg_pos_rat_q2, ``sin_reduce_arg_pos_rat_q3][j]!
  let hrc := mkAppN (Lean.mkConst argLemma)
    #[natLitShared a, natLitShared b, natLitShared Pc, natLitShared Q, natLitShared qq,
      natLitShared u, natLitShared v,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return (#[k, qq, j, E, Pc, Q, u, v], #[piPf, xE, rcvE, hrc])

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
  -- the series then raises to a power. Round it onto `·/2^vb`, wide enough that the rounding sits
  -- well inside the radius, and evaluate the series at the coarser argument; `cos_arg_round` puts
  -- the difference back into the radius. Below that width there is nothing to gain, so skip it.
  -- The rounding costs a little precision, which has to be bought back by running the series
  -- tighter, and that is itself expensive. Buying it from the rounding width instead is far
  -- cheaper: at `vr ≈ 2^12·Dp` the inner precision need only rise by about a thousandth, where
  -- rounding hard enough to need double the precision gives the saving straight back.
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
