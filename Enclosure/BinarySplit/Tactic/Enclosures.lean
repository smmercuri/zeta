module

public import Enclosure
public import Enclosure.Complex
public import Enclosure.BinarySplit.Reduce.Log
public import Enclosure.BinarySplit.Tactic.Engine
public import Enclosure.BinarySplit.Tactic.Recognizer
public import Enclosure.BinarySplit.Tactic.Exp
public import Enclosure.BinarySplit.Tactic.Sin
public import Enclosure.BinarySplit.Tactic.Cos
public import Enclosure.BinarySplit.Tactic.Log
public import Enclosure.BinarySplit.Tactic.Log2
public import Enclosure.BinarySplit.Tactic.Sqrt
public import Enclosure.BinarySplit.Tactic.Pi
public import Enclosure.BinarySplit.Tactic.Reduce

/-!
# Building `IsNear` enclosures from certified function bounds

This file carries an enclosure as a record `RNear`: the proof `Expr` of `Real.IsNear x …`
together with its `(neg, cn, cd, rn, rd)` fields as metavalues. Each combinator
(`addNear`/`subNear`/`mulNear`, the function builders `mkExpNear`/`mkLogNearOf`/…) computes its
result tuple while applying the matching real lemma; `CNear` pairs two `RNear`s for the real and
imaginary parts of a complex value. Together they assemble enclosures of composite real and
complex values.
-/
@[expose] public section


namespace BSN
open Enclosure

open Lean Meta

/-! The enclosed real of a combinator's result is a fixed function of its inputs' reals, so build it
directly (matching the notation instances the `Real.IsNear.*Lit`/`neg` conclusions use) instead of
re-deriving it from the assembled proof by `inferType`. Any mismatch is caught by the kernel when
the result feeds the next lemma. -/

/-- `x * y` on `ℝ` (`@HMul.hMul ℝ ℝ ℝ (instHMul Real.instMul) x y`). -/
meta def mkMulR (x y : Expr) : Expr :=
  mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHMul [.zero]) realTyE (mkConst ``Real.instMul),
      x, y]

/-- `x + y` on `ℝ`. -/
meta def mkAddR (x y : Expr) : Expr :=
  mkAppN (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHAdd [.zero]) realTyE (mkConst ``Real.instAdd),
      x, y]

/-- `x - y` on `ℝ`. -/
meta def mkSubR (x y : Expr) : Expr :=
  mkAppN (mkConst ``HSub.hSub [.zero, .zero, .zero])
    #[realTyE, realTyE, realTyE,
      mkApp2 (mkConst ``instHSub [.zero]) realTyE (mkConst ``Real.instSub),
      x, y]

/-- `Real.pi`, the enclosed real of a `π` tier / Machin build. -/
meta def mkPiE : Expr := mkConst ``Real.pi

/-- `x⁻¹` on `ℝ` (`@Inv.inv ℝ Real.instInv x`). -/
meta def mkInvR (x : Expr) : Expr :=
    mkApp3 (mkConst ``Inv.inv [.zero]) realTyE (mkConst ``Real.instInv) x

/-- `∑ i ∈ Finset.Ico a b, f i`, the enclosed real of a finite-sum leaf/combine
(`@Finset.sum ℕ ℝ Real.instAddCommMonoid (Finset.Ico a b) f`). -/
meta def mkFinsetIcoSumE (f : Expr) (a b : ℕ) : Expr :=
  mkAppN (mkConst ``Finset.sum [.zero, .zero])
    #[mkConst ``Nat, realTyE, mkConst ``Real.instAddCommMonoid,
      mkAppN (mkConst ``Finset.Ico [.zero])
        #[mkConst ``Nat, mkConst ``Nat.instPreorder, mkConst ``Nat.instLocallyFiniteOrder,
          natLitShared a, natLitShared b],
      f]

/-- `∑ i ∈ Finset.range n, f i`, the enclosed real of a `range`-sum result
(`@Finset.sum ℕ ℝ Real.instAddCommMonoid (Finset.range n) f`). -/
meta def mkFinsetRangeSumE (f : Expr) (n : ℕ) : Expr :=
  mkAppN (mkConst ``Finset.sum [.zero, .zero])
    #[mkConst ``Nat, realTyE, mkConst ``Real.instAddCommMonoid,
      mkApp (mkConst ``Finset.range) (natLitShared n), f]

/-- `Complex.log ⟨sfrac false p q, sfrac false r q⟩`, the argument of the `clog_re_eq`/`clog_im_eq`
projections (`Complex.log (Complex.mk (sfrac false p q) (sfrac false r q))`). -/
meta def mkClogZE (p r q : ℕ) : Expr :=
  mkApp (mkConst ``Complex.log)
    (mkApp2 (mkConst ``Complex.mk) (mkSfracR false p q) (mkSfracR false r q))

open Elab Tactic in
/-- Close a `Bool = true` (or defeq) goal by an unchecked assign of `reflBoolTrue` (raw
`MVarId.assign`), leaving the single `Nat.beq`/`ble` check to the kernel. -/
elab "quickRfl" : tactic => liftMetaFinishingTactic (·.assign reflBoolTrue)

/-- A built real enclosure: a kernel proof of `Real.IsNear x neg cn cd rn rd` (the real `x` lives in
the proof's type), plus that data as metavalues for the next combinator. -/
structure RNear where
  proof : Expr
  /-- The enclosed real `x` (the subject of `proof : Real.IsNear x …`), carried so operations do
  not re-derive it from `proof` by `inferType` on every use. -/
  x : Expr
  neg : Bool
  cn : ℕ
  cd : ℕ
  rn : ℕ
  rd : ℕ

/-- A built complex (rectangle) enclosure: independent real enclosures of the real and imaginary
parts, sharing the proof of `Complex.IsNear z …` once assembled. -/
structure CNear where
  re : RNear
  im : RNear

/-! ### Function builders -/

/-- Target dyadic precision for `renorm`: centre/radius denominators are capped at `2 ^ renormBits`.
Set far above the certificate precision, so only a deep computation gets coarsened. -/
meta def renormBits : ℕ := 1024

/-- Floor the centre `cn/cd` and ceil the radius `rn/rd` (absorbing the centre drop `δ`) onto the
dyadic grid `·/B`, then `gcd`-reduce, returning `(cn', cd', rn', rd')`. The shared rounding
arithmetic of `renormFields?` (scale-aware `B`) and `recentreToBits` (fixed `B = 2^bits`). -/
meta def roundFieldsAt (cn cd rn rd B : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let cnF := (cn * B) / cd                  -- floor of cn/cd onto ·/B
  let cnErr := cn * B - cnF * cd            -- = (cn·B) mod cd, in [0, cd)
  let Nnum := rn * (cd * B) + cnErr * rd    -- numerator of rn/rd + δ over rd·cd·B
  let Dden := rd * (cd * B)
  let rnF := (Nnum * B + Dden - 1) / Dden   -- ceil of (rn/rd + δ) onto ·/B
  let gc := Nat.gcd cnF B
  let gr := Nat.gcd rnF B
  (cnF / gc, B / gc, rnF / gr, B / gr)

/-- Wrap a rounded field set `(cn', cd', rn', rd')` for `r` into `Real.IsNear.recentre'`, carrying
`r`'s enclosed real and original fields; the single `reflBoolTrue` discharges `recentreOk`, which
carries all six recentre side conditions. Shared by `renorm`, `recentreToBits`, and `litNear`. -/
meta def mkRecentreNear (r : RNear) (cn' cd' rn' rd' : ℕ) : MetaM RNear := do
  let proof := mkAppN (mkConst ``Real.IsNear.recentre')
    #[r.x, toExpr r.neg, natLitShared r.cn, natLitShared r.cd, natLitShared r.rn, natLitShared r.rd,
      natLitShared cn', natLitShared cd', natLitShared rn', natLitShared rd',
      r.proof, reflBoolTrue]
  return { proof, x := r.x, neg := r.neg, cn := cn', cd := cd', rn := rn', rd := rd' }

/-- The pure rounding arithmetic of `renorm`: `none` when the fields already fit under the
scale-aware cap, else the floored/ceiled, `gcd`-reduced `(cn', cd', rn', rd')`. Shared by `renorm`
and the paired rectangle path in `Tactic.Named`. -/
meta def renormFields? (cn cd rn rd : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  -- Scale-aware cap: keep ~`renormBits` SIGNIFICANT bits. For a value of magnitude `2^{-e}`
  -- the denominator cap is `2^{renormBits+e}`, so a value many orders below `2^{-renormBits}`
  -- retains its significant bits rather than collapsing to `[±2^{-renormBits}]`. Values of
  -- magnitude `≥ 1` use the plain `2^{renormBits}` cap.
  let e :=
    if cn != 0 then cd.log2 - cn.log2
    else if rn != 0 then rd.log2 - rn.log2
    else 0
  let B := 2 ^ (renormBits + min e 4096)
  if cd ≤ B && rd ≤ B then
    none
  else
    some (roundFieldsAt cn cd rn rd B)

/-- Renormalize an enclosure. If both denominators already fit under `2 ^ renormBits`, keep it
as-is. Otherwise round the centre down and the radius up onto the dyadic grid `·/2^renormBits`
(absorbing the centre drop `δ ≤ 2^{-renormBits}` into the radius), `gcd`-reduce, and wrap
`Real.IsNear.recentre`. This caps field magnitudes under repeated multiplication. Applied after
every combine. -/
meta def renorm (r : RNear) : MetaM RNear := do
  match renormFields? r.cn r.cd r.rn r.rd with
  | none => return r
  | some (cn', cd', rn', rd') => mkRecentreNear r cn' cd' rn' rd'

/-- Extra dyadic bits kept above `⌈log₂(2D)⌉` when capping a trig argument at working precision
in `recentreToBits`. Small headroom so the rounding drop stays well inside the separation margin. -/
meta def argRecentreGuard : ℕ := 2

/-- Round an enclosure's centre/radius onto the dyadic grid `·/2^bits` (floor the centre, ceil the
radius to absorb the drop), `gcd`-reduce, and wrap `Real.IsNear.recentre`. Returns the enclosure
unchanged when both denominators already fit under `2^bits`. Caps a trig argument at working
precision before range reduction, so the reduced argument and its series leaves stay small. -/
meta def recentreToBits (bits : ℕ) (r : RNear) : MetaM RNear := do
  let B := 2 ^ bits
  if r.cd ≤ B && r.rd ≤ B then return r
  let (cn', cd', rn', rd') := roundFieldsAt r.cn r.cd r.rn r.rd B
  mkRecentreNear r cn' cd' rn' rd'

/-- Rewrite a leaf enclosure's symbolic result fields (a sin/cos `mp − mn` centre, an image
builder's radius sum, a sqrt midpoint `a + b`, a range-reduced log's centre) into single
`gcd`-reduced numeral literals, via the exact case of `Real.IsNear.recentre` (reduced fields equal
the originals, so `δ = 0` and both `Nat.ble` conditions hold by `reflBoolTrue`). Leaves only. -/
meta def litNear (r : RNear) : MetaM RNear := do
  let gc := Nat.gcd r.cn r.cd
  let gr := Nat.gcd r.rn r.rd
  mkRecentreNear r (r.cn / gc) (r.cd / gc) (r.rn / gr) (r.rd / gr)

/-- Transport an enclosure onto the left side `y` of an equality `he : y = x` of enclosed reals,
keeping the fields (`Real.IsNear.of_eq`). Renames a builder's assembled real to the value the
caller asked about (a `Finset` sum, a range-reduced `arctan`, a `Complex.log` component). The
caller builds and passes the LHS `y` directly (it is the conclusion of the lemma that produced
`he`), so it need not be read back off `he`'s type. -/
meta def ofEqNear (y he : Expr) (r : RNear) : MetaM RNear := do
  let proof := mkAppN (mkConst ``Real.IsNear.of_eq)
    #[y, r.x, toExpr r.neg, natLitShared r.cn, natLitShared r.cd,
      natLitShared r.rn, natLitShared r.rd, he, r.proof]
  return { r with proof, x := y }

/-- Enclose `Real.exp (u/v)` (nonnegative; `v = 1` is the integer case) to radius `1/D`: the `exp`
certificate is already an `IsNear` enclosure, paired with the numeric dyadic `p/Q`. -/
meta def mkExpNear (u v D : ℕ) : MetaM RNear := do
  let (p, Q, _, _) ← expCore u v D
  let (proof, _, _, _, _, _) ← mkExpCert u v D (if v == 1 then 0 else 1)
  -- `mkExpCert` recasts the `v = 1` case to `Real.exp ↑u` (`exp_int_of_rat`); otherwise the
  -- enclosed real is `Real.exp (↑u/↑v)`.
  let x := mkRealFn ``Real.exp (if v == 1 then mkNatCastR u else mkCastDivR u v)
  return { proof, x, neg := false, cn := p, cd := Q, rn := 1, rd := D }

/-- Shared body of `mkSinNear`/`mkCosNear`. Run the even/odd positive-cert builder `mkPos`; its
certificate is already an `IsNear` enclosure with literal signed-centre fields `(neg, cn, Q)`. -/
private meta def mkSignedCertNear (mkPos : ℕ → ℕ → ℕ → MetaM (Expr × Bool × ℕ × ℕ)) (resFn : Name)
    (u v D : ℕ) : MetaM RNear := do
  let (app, neg, cn, Q) ← mkPos u v D
  return { proof := app, x := mkApp (mkConst resFn) (mkCastDivR u v), neg, cn, cd := Q,
           rn := 1, rd := D }

/-- Shared body of `mkSinImageNear`/`mkCosImageNear`. For an enclosure `a` of `x` with a dyadic
centre `±cn/cd`, certify the function at the centre's magnitude via `mkCert` (inner precision
`1/D`); a negative centre routes the certificate through the function's negative-argument lemma
`negLemma` (`sin_neg_of_bound` flips the value's sign, `cos_neg_of_bound` keeps it); then widen
by `a`'s radius through `imageLemma` (`sin_image`/`cos_image`). The centre equation `hc` is
`sfrac_false_div`/`sfrac_true_div` as the sign requires. -/
private meta def mkImageNear (mkCert : ℕ → ℕ → ℕ → MetaM RNear) (negLemma imageLemma resFn : Name)
    (negFlips : Bool) (a : RNear) (D : ℕ) : MetaM RNear := do
  let a ← recentreToBits ((2 * D).log2 + argRecentreGuard) a
  let base ← mkCert a.cn a.cd D
  let cert ← do
    if a.neg then
      let proof := mkAppN (mkConst negLemma)
        #[natLitShared a.cn, natLitShared a.cd, toExpr base.neg, natLitShared base.cn,
          natLitShared base.cd,
          natLitShared base.rn, natLitShared base.rd, base.proof]
      -- `sin_neg_of_bound`/`cos_neg_of_bound` conclude `Real.f ((-↑a.cn)/↑a.cd)`.
      let xNeg := mkRealFn resFn (mkNegCastDivR a.cn a.cd)
      let outNeg := if negFlips then !base.neg else base.neg
      pure { base with proof, x := xNeg, neg := outNeg }
    else pure base
  let hc := mkApp2 (mkConst (if a.neg then ``sfrac_true_div else ``sfrac_false_div))
    (natLitShared a.cn) (natLitShared a.cd)
  let proof := mkAppN (mkConst imageLemma)
    #[a.x, cert.x.appArg!,
      toExpr a.neg, natLitShared a.cn, natLitShared a.cd, natLitShared a.rn, natLitShared a.rd,
      toExpr cert.neg, natLitShared cert.cn, natLitShared cert.cd, natLitShared cert.rn,
      natLitShared cert.rd, a.proof, hc, cert.proof, reflBoolTrue, reflBoolTrue]
  litNear { proof, x := mkApp (mkConst resFn) a.x, neg := cert.neg, cn := cert.cn, cd := cert.cd,
            rn := cert.rn * a.rd + a.rn * cert.rd, rd := cert.rd * a.rd }

/-- Enclose `Real.sin (u/v)` (nonnegative; `v = 1` is the integer case) to radius `1/D`: the
even/odd `sin` certificate from `mkSinPos`, through `mkSignedCertNear`. -/
meta def mkSinNear (u v D : ℕ) : MetaM RNear := mkSignedCertNear mkSinPos ``Real.sin u v D

/-- `mkSinNear` with automatic range reduction: arguments at `2` or above (past `π/2`) go
through the quadrant reduction at the exact rational centre, so image certificates at large
centres stay cheap. -/
meta def mkSinNearAuto (u v D : ℕ) : MetaM RNear := do
  if u ≥ 2 * v && 0 < v then
    let (proof, neg, cn, Qd) ← mkTrigPosReduced false u v D
    return { proof, x := mkApp (mkConst ``Real.sin) (mkCastDivR u v), neg, cn, cd := Qd,
             rn := 1, rd := D }
  else mkSinNear u v D

/-- `sin` of an enclosure (either centre sign): `mkImageNear` at `mkSinNear`/`sin_image`. -/
meta def mkSinImageNear (a : RNear) (D : ℕ) : MetaM RNear :=
  mkImageNear mkSinNearAuto ``sin_neg_of_bound ``Real.IsNear.sin_image ``Real.sin true a D

/-- Enclose `Real.log n` for odd `n` in the artanh convergence range (`2u² ≤ v²` with
`u=(n-1)/2, v=(n+1)/2`, i.e. `n ≤ 5`): certify `log((v+u)/(v-u)) = log(n/1)` and recast to `log n`.
Larger `n` needs log range reduction (`mkLogRatReduceNear` with `b = 1`). -/
meta def mkLogNear (n D : ℕ) : MetaM RNear := do
  let u := (n - 1) / 2
  let v := (n + 1) / 2
  let (app, p, Q) ← mkLogPos u v D
  let proof := mkAppN (mkConst ``log_nat_of_cert)
    #[natLitShared (v + u), natLitShared (v - u), natLitShared n, toExpr false, natLitShared p,
      natLitShared Q,
      natLitShared 1,
      natLitShared D, reflBoolTrue, reflBoolTrue, app]
  return { proof, x := mkRealFn ``Real.log (mkNatCastR n), neg := false, cn := p, cd := Q,
           rn := 1, rd := D }

/-- Raw log enclosure: a proof of `Real.IsNear (log(↑S/↑Dd)) false p Q 1 D` with the literals
`S = v+u`, `Dd = v-u`, plus `(p, Q)`. Certifies through `mkLogPos` (`log_dyadic_bound`). -/
meta def mkLogCertRaw (u v D : ℕ) : MetaM (Expr × ℕ × ℕ) := mkLogPos u v D

/-- `log(a/b)` via range reduction (any positive rational, `a ≥ b`): pick `k = ⌊log₂(a/b)⌋` so
`(a/b)/2ᵏ = a/(b·2ᵏ) ∈ [1,2)`, certify that reduced log at `1/D` and `log 2` at `1/E`, then combine
with `log_rat_reduce_isNear`. The reduced cert's literal argument `(a+b·2ᵏ)±(a−b·2ᵏ)` equals the
literal `2a` / `b·2^{k+1}` passed for the `S`/`Dd` slots, so the `hr` slot matches syntactically.
Integer `log n` is the `b = 1` call. -/
meta def mkLogRatReduceNear (a b D E : ℕ) : MetaM RNear := do
  let k := Nat.log 2 (a / b)
  let pk := b * 2 ^ k
  let (hr, pr, Qr) ← mkLogCertRaw (a - pk) (a + pk) D
  -- `log 2` certificate: a shared named tier (`log2_near_15/50`, each kernel-checked once) serves
  -- any `E ≤ 10⁵⁰` via `mkLog2Tier?`, used at full precision (it is at least as precise as asked,
  -- so it only tightens). Build fresh only above `1/10⁵⁰`.
  let (Euse, p2, Q2, h2) ← do
    match ← mkLog2Tier? E with
    | some r => pure r
    | none =>
      let (h2raw, p2, Q2) ← mkLogCertRaw 1 3 E
      pure (E, p2, Q2,
            mkAppN (mkConst ``log_two_eq)
            #[natLitShared p2, natLitShared Q2, natLitShared E, h2raw])
  let proof := mkAppN (mkConst ``log_rat_reduce_isNear)
    #[natLitShared a, natLitShared b, natLitShared k, natLitShared (2 * a),
      natLitShared (b * 2 ^ (k + 1)),
      natLitShared pr, natLitShared Qr, natLitShared p2, natLitShared Q2,
      natLitShared D, natLitShared Euse, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, hr, h2, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue]
  litNear { proof, x := mkRealFn ``Real.log (mkCastDivR a b), neg := false,
            cn := pr * Q2 + k * p2 * Qr, cd := Qr * Q2, rn := Euse + k * D, rd := D * Euse }

/-- Enclose `Real.cos (u/v)` (the even mirror of `mkSinNear`): the even/odd `cos` certificate from
`mkCosPos`, through `mkSignedCertNear`. -/
meta def mkCosNear (u v D : ℕ) : MetaM RNear := mkSignedCertNear mkCosPos ``Real.cos u v D

/-- `mkCosNear` with automatic range reduction (see `mkSinNearAuto`). -/
meta def mkCosNearAuto (u v D : ℕ) : MetaM RNear := do
  if u ≥ 2 * v && 0 < v then
    let (proof, neg, cn, Qd) ← mkTrigPosReduced true u v D
    return { proof, x := mkApp (mkConst ``Real.cos) (mkCastDivR u v), neg, cn, cd := Qd,
             rn := 1, rd := D }
  else mkCosNear u v D

/-- `cos` of an enclosure (either centre sign): `mkImageNear` at `mkCosNear`/`cos_image`. -/
meta def mkCosImageNear (a : RNear) (D : ℕ) : MetaM RNear :=
  mkImageNear mkCosNearAuto ``cos_neg_of_bound ``Real.IsNear.cos_image ``Real.cos false a D

/-- Exact constant enclosure of the rational `cn/cd` (radius `0`), via `Real.IsNear.const`. -/
meta def mkConstNear (cn cd : ℕ) : MetaM RNear := do
  let proof :=
      mkAppN (mkConst ``Real.IsNear.const) #[toExpr false, natLitShared cn, natLitShared cd]
  return { proof, x := mkSfracR false cn cd, neg := false, cn, cd, rn := 0, rd := 1 }

/-- Exact constant enclosure of a signed rational (radius `0`). Denominators above `2^renormBits`
are capped by `renorm`. -/
meta def mkRatConstNear (q : ℚ) : MetaM RNear := do
  let neg := decide (q < 0)
  let proof := mkAppN (mkConst ``Real.IsNear.const)
    #[toExpr neg, natLitShared q.num.natAbs, natLitShared q.den]
  renorm { proof, x := mkSfracR neg q.num.natAbs q.den, neg, cn := q.num.natAbs, cd := q.den,
           rn := 0, rd := 1 }

/-- Enclose `√(N/M)` as an `RNear`: midpoint `(a+b)/(2Q)` ± half-width `(b−a)/(2Q)`, straight
from the square-to-verify `IsNear` enclosure `mkSqrtEncl` (literalized by `litNear`). -/
meta def mkSqrtNear (N M D : ℕ) : MetaM RNear := do
  if let some (p, xv, neg, cn, cd, rn, rd) := (← sqrtNearCache.get)[(N, M, D)]? then
    return { proof := p, x := xv, neg, cn, cd, rn, rd }
  let (encl, a, b, Q) ← mkSqrtEncl N M D
  let xv := mkRealFn ``Real.sqrt (mkCastDivR N M)
  let r ← litNear { proof := encl, x := xv, neg := false, cn := a + b, cd := 2 * Q, rn := b - a,
                    rd := 2 * Q }
  sqrtNearCache.modify (·.insert (N, M, D) (r.proof, r.x, r.neg, r.cn, r.cd, r.rn, r.rd))
  return r

/-- `√` of an enclosure (`S ≥ 0`, lower endpoint `≥ 0`): square-to-verify the two rational
endpoints `lo`,`hi` at a common `Q = 2ᵏ`, then `√S ∈ [a/Q, b/Q]` via `sqrt_image`. -/
meta def mkSqrtImageNear (S : RNear) (D : ℕ) : MetaM RNear := do
  if S.neg then throwError "mkSqrtImageNear: negative centre not supported"
  let cnrd := S.cn * S.rd
  let rncd := S.rn * S.cd
  if cnrd ≤ rncd then
    throwError "mkSqrtImageNear: the enclosure straddles zero (argument too close to 0); the \
      value cannot be separated from 0. Widen the bracket or increase precision"
  let Q := dyadicDenom D
  let Mden := S.cd * S.rd
  let Nlo := (cnrd - rncd) * Q ^ 2
  let Nhi := (cnrd + rncd) * Q ^ 2
  let a := Nat.sqrt (Nlo / Mden)
  let b := Nat.sqrt (Nhi / Mden) + 1
  let proof := mkAppN (mkConst ``Real.IsNear.sqrt_image)
    #[S.x, natLitShared S.cn, natLitShared S.cd, natLitShared S.rn, natLitShared S.rd,
      natLitShared a, natLitShared b, natLitShared Q, S.proof, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  litNear { proof, x := mkRealFn ``Real.sqrt S.x, neg := false, cn := a + b, cd := 2 * Q,
            rn := b - a, rd := 2 * Q }

/-! ### Real combinators (compute the result tuple, apply the matching lemma) -/

/-- Negation: flip the sign flag; apply `Real.IsNear.neg`. -/
meta def negNear (a : RNear) : MetaM RNear := do
  let proof := mkAppN (mkConst ``Real.IsNear.neg)
    #[a.x, toExpr a.neg, natLitShared a.cn, natLitShared a.cd, natLitShared a.rn, natLitShared a.rd,
      a.proof]
  return { a with proof := proof, x := mkNegR a.x, neg := !a.neg }

/-- The signed centre of `a ± b` (`sub` negates `b`): the result sign and the centre-numerator
magnitude over the common denominator `a.cd * b.cd`. Shared by `addNear`/`subNear` and the
paired rectangle combines in `Tactic.Named`. -/
meta def addCentreFields (a b : RNear) (sub : Bool) : Bool × ℕ :=
  let sx : ℤ := (if a.neg then -1 else 1) * a.cn * b.cd
  let sy : ℤ := (if b.neg then -1 else 1) * b.cn * a.cd
  let s := if sub then sx - sy else sx + sy
  (decide (s < 0), s.natAbs)

/-- The `gcd`-reduced literal result fields `(cn', cd', rn', rd')` of an add-like combine with
pre-reduction centre numerator `cn` (from `addCentreFields`). Shared with the paired rectangle
combines, like `addCentreFields`. -/
meta def addLikeFields (a b : RNear) (cn : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let cd := a.cd * b.cd
  let rn := a.rn * b.rd + b.rn * a.rd
  let rd := a.rd * b.rd
  let gc := Nat.gcd cn cd; let gr := Nat.gcd rn rd
  (cn / gc, cd / gc, rn / gr, rd / gr)

/-- The shared `add`/`sub` assembly via the literal-output lemma `thm` (`addLit`/`subLit`): compute
the signed sum centre `s`, `gcd`-reduce the result centre/radius to literals `cn' cd' rn' rd'`, and
pin them into the lemma with the add-stage numerator `s.natAbs`; every side condition is
`reflBoolTrue`. -/
private meta def mkAddLike (thm : Name) (signed sub : Bool) (a b : RNear) (neg : Bool) (cn : ℕ) :
    MetaM RNear := do
  let (cn', cd', rn', rd') := addLikeFields a b cn
  -- the sign-specialized variants carry no Bool args (the sign case is baked into the lemma);
  -- `signed` selects the general numPos form (only for combinations a variant can't cover)
  let boolArgs : Array Expr := if signed then #[toExpr a.neg, toExpr b.neg, toExpr neg] else #[]
  -- The general `addLit`/`subLit` still takes its nine conditions separately; the sign variants
  -- take the centre condition and then `addLitOk`, which carries the other eight.
  let condArgs : Array Expr :=
    if signed then
      #[reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
        reflBoolTrue, reflBoolTrue, reflBoolTrue]
    else #[reflBoolTrue, reflBoolTrue]
  let proof := mkAppN (mkConst thm)
    (#[a.x, b.x] ++ boolArgs ++
    #[natLitShared a.cn, natLitShared a.cd, natLitShared a.rn, natLitShared a.rd,
      natLitShared b.cn, natLitShared b.cd, natLitShared b.rn, natLitShared b.rd,
      natLitShared cn, natLitShared cn', natLitShared cd', natLitShared rn', natLitShared rd',
      a.proof, b.proof] ++ condArgs)
  renorm { proof, x := if sub then mkSubR a.x b.x else mkAddR a.x b.x,
           neg, cn := cn', cd := cd', rn := rn', rd := rd' }

/-- The sign-specialized `addLit` variant for input signs `(nx, ny)` and result sign `nR`
(`none` = the combination is impossible for exact arithmetic; fall back to the general lemma). -/
private meta def addLitVariant : Bool → Bool → Bool → Option Name
  | false, false, false => some ``Real.IsNear.addLit_ff
  | true,  true,  true  => some ``Real.IsNear.addLit_tt
  | false, true,  false => some ``Real.IsNear.addLit_ft_p
  | false, true,  true  => some ``Real.IsNear.addLit_ft_n
  | true,  false, false => some ``Real.IsNear.addLit_tf_p
  | true,  false, true  => some ``Real.IsNear.addLit_tf_n
  | _,     _,     _     => none

/-- The sign-specialized `subLit` variant (same convention). -/
private meta def subLitVariant : Bool → Bool → Bool → Option Name
  | false, false, false => some ``Real.IsNear.subLit_ff_p
  | false, false, true  => some ``Real.IsNear.subLit_ff_n
  | false, true,  false => some ``Real.IsNear.subLit_ft
  | true,  false, true  => some ``Real.IsNear.subLit_tf
  | true,  true,  false => some ``Real.IsNear.subLit_tt_p
  | true,  true,  true  => some ``Real.IsNear.subLit_tt_n
  | _,     _,     _     => none

/-- Addition: result centre is the signed sum over the common denominator; the sign-specialized
`addLit_*` variant emits literals with a `numPos`-free centre condition. -/
meta def addNear (a b : RNear) : MetaM RNear := do
  let (neg, cn) := addCentreFields a b false
  match addLitVariant a.neg b.neg neg with
  | some thm => mkAddLike thm false false a b neg cn
  | none => mkAddLike ``Real.IsNear.addLit true false a b neg cn

/-- Subtraction: as `addNear` but with the second centre negated (`subLit_*`). -/
meta def subNear (a b : RNear) : MetaM RNear := do
  let (neg, cn) := addCentreFields a b true
  match subLitVariant a.neg b.neg neg with
  | some thm => mkAddLike thm false true a b neg cn
  | none => mkAddLike ``Real.IsNear.subLit true true a b neg cn

/-- The sign-specialized `mulLit` variant for input signs `(nx, ny)`: the conclusion's sign is
the literal `nx ^^ ny` evaluates to, so no `Bool.xor` ever reaches a downstream kernel check. -/
private meta def mulLitVariant : Bool → Bool → Name
  | false, false => ``Real.IsNear.mulLit_ff
  | false, true  => ``Real.IsNear.mulLit_ft
  | true,  false => ``Real.IsNear.mulLit_tf
  | true,  true  => ``Real.IsNear.mulLit_tt

/-- Multiplication: sign `xor`, magnitudes multiply, radius is the exact interval-product bound;
the sign-specialized `mulLit_*` variant emits `gcd`-reduced literals directly (with a literal
result sign), tied to the symbolic product by `reflBoolTrue`. -/
meta def mulNearRaw (a b : RNear) : MetaM RNear := do
  let cn := a.cn * b.cn; let cd := a.cd * b.cd
  let rn := a.cn * b.rn * b.cd * a.rd + b.cn * a.rn * a.cd * b.rd + a.rn * b.rn * a.cd * b.cd
  let rd := a.cd * b.cd * a.rd * b.rd
  let gc := Nat.gcd cn cd; let gr := Nat.gcd rn rd
  let cn' := cn / gc; let cd' := cd / gc; let rn' := rn / gr; let rd' := rd / gr
  let proof := mkAppN (mkConst (mulLitVariant a.neg b.neg))
    #[a.x, b.x,
      natLitShared a.cn, natLitShared a.cd, natLitShared a.rn, natLitShared a.rd,
      natLitShared b.cn, natLitShared b.cd, natLitShared b.rn, natLitShared b.rd,
      natLitShared cn', natLitShared cd', natLitShared rn', natLitShared rd',
      a.proof, b.proof, reflBoolTrue]
  return { proof, x := mkMulR a.x b.x, neg := a.neg ^^ b.neg, cn := cn', cd := cd',
           rn := rn', rd := rd' }

meta def mulNear (a b : RNear) : MetaM RNear := do
  renorm (← mulNearRaw a b)

/-- Complex absolute value. `|z| = √(z.re·z.re + z.im·z.im)`: square each component (`mulNear`),
add (`addNear`), then `√` of the resulting nonnegative enclosure (`mkSqrtImageNear`). Returns an
`RNear` enclosing `|z|`. -/
meta def cAbsNear (z : CNear) (D : ℕ) : MetaM RNear := do
  let re2 ← mulNear z.re z.re
  let im2 ← mulNear z.im z.im
  let s ← addNear re2 im2
  mkSqrtImageNear s D

/-! ### Complex (rectangle) combinators

A `CNear` is a rectangle: an `RNear` for the real part and one for the imaginary part. Complex
arithmetic is componentwise interval arithmetic, each component assembled from the real
combinators. Each builder returns the result rectangle. -/

/-- Complex negation: negate each component (`negNear`). -/
meta def cnegNear (z : CNear) : MetaM CNear := do
  return { re := ← negNear z.re, im := ← negNear z.im }

/-- Complex addition: add rectangles componentwise (`(z+w).re = z.re+w.re`,
`(z+w).im = z.im+w.im`). -/
meta def caddNear (z w : CNear) : MetaM CNear := do
  return { re := ← addNear z.re w.re, im := ← addNear z.im w.im }

/-- Complex subtraction: subtract rectangles componentwise. -/
meta def csubNear (z w : CNear) : MetaM CNear := do
  return { re := ← subNear z.re w.re, im := ← subNear z.im w.im }

/-- Complex multiplication: `(z·w).re = z.re·w.re − z.im·w.im`, `(z·w).im = z.re·w.im + z.im·w.re`,
each assembled from two `mulNear`s and one `subNear`/`addNear`. -/
meta def cmulNear (z w : CNear) : MetaM CNear := do
  let rr ← mulNear z.re w.re
  let ii ← mulNear z.im w.im
  let ri ← mulNear z.re w.im
  let ir ← mulNear z.im w.re
  return { re := ← subNear rr ii, im := ← addNear ri ir }

/-! ### Finite-sum enclosures

A certified enclosure of `∑ i in Finset.Ico a b, f i` by binary recursion on the interval: split at
the midpoint (`sum_Ico_consec_real`), recurse on each half, combine with `addNear`. Base cases: a
width-one interval (`f a`, via the caller's per-term builder) and the empty interval (`0`). The
outer recursion is not a `binarySplit` (the per-term centres are arbitrary `term` outputs). -/

/-- Enclose `∑ i ∈ Finset.Ico a b, f i`, given a per-term builder `encl i` enclosing `f i`. Binary
recursion on `[a,b)`: split at the midpoint and combine the halves with `addNear` (renormalized
literal fields), transporting along `sum_Ico_consec_real`. `f` is the summand Expr (`ℕ → ℝ`). -/
meta partial def mkFinsetIcoSumNear (encl : ℕ
      → MetaM RNear) (f : Expr) (a b : ℕ) : MetaM RNear := do
  if a ≥ b then
    let proof := mkAppN (mkConst ``Real.IsNear.sum_Ico_empty)
      #[f, natLitShared a, natLitShared b, reflBoolTrue]
    return { proof, x := mkFinsetIcoSumE f a b, neg := false, cn := 0, cd := 1, rn := 0, rd := 1 }
  else if a + 1 == b then
    let term ← encl a
    let he :=
        mkAppN (mkConst ``sum_Ico_width_one_real) #[f, natLitShared a, natLitShared b, reflBoolTrue]
    ofEqNear (mkFinsetIcoSumE f a b) he term
  else
    let m := (a + b) / 2
    let hl ← mkFinsetIcoSumNear encl f a m
    let hr ← mkFinsetIcoSumNear encl f m b
    let hsum ← addNear hl hr
    let he := mkAppN (mkConst ``sum_Ico_consec_real)
      #[f, natLitShared a, natLitShared m, natLitShared b, reflBoolTrue, reflBoolTrue]
    ofEqNear (mkFinsetIcoSumE f a b) he hsum

/-- A recognised finite-index-set shape (`Nat` index): `Finset.range n` or `Finset.Ico a b`. -/
inductive FinsetShape where
  | range (n : ℕ)
  | ico (a b : ℕ)
  deriving Repr

/-- Enclose `∑ i ∈ S, f i` for a recognised `Finset` shape `S`, given the per-term builder
`encl`. -/
meta def mkFinsetSumNear (encl : ℕ → MetaM RNear) (f : Expr) : FinsetShape → MetaM RNear
  | .ico a b => mkFinsetIcoSumNear encl f a b
  | .range n => do
    let r ← mkFinsetIcoSumNear encl f 0 n
    let he := mkAppN (mkConst ``sum_range_eq_Ico_real) #[f, natLitShared n]
    ofEqNear (mkFinsetRangeSumE f n) he r

/-- Enclose `Real.log (a/b)` for a positive rational `a/b ≥ 1` (`a ≥ b`). When `a/b` is in the
artanh range (`2(a-b)² ≤ (a+b)²`), certify it directly with a single gcd-reduced split
(`mkLogFracPos`, recast to `log(a/b)` by the weighted `logfrac_isNear`). Otherwise range-reduce
`a/b` to `[1,2)` via `mkLogRatReduceNear`. -/
meta def mkLogRatNear (a b D E : ℕ) : MetaM RNear := do
  if let some (p, xv, neg, cn, cd, rn, rd) := (← logNearCache.get)[(a, b, D, E)]? then
    return { proof := p, x := xv, neg, cn, cd, rn, rd }
  let r ← do
    if Nat.ble (2 * (a - b) ^ 2) ((a + b) ^ 2) then
      let (proof, p, Q) ← mkLogFracPos a b D
      pure { proof, x := mkRealFn ``Real.log (mkCastDivR a b), neg := false,
             cn := p, cd := Q, rn := 1, rd := D }
    else
      mkLogRatReduceNear a b D E
  logNearCache.modify (·.insert (a, b, D, E) (r.proof, r.x, r.neg, r.cn, r.cd, r.rn, r.rd))
  return r

/-- Enclose `Real.log (sfrac false pn pd)` for any positive rational `pn/pd` (in canonical `sfrac`
form, so the argument can then be transported onto any surface form via `isNear_log_arg`). For
`pn ≥ pd` it certifies `pn/pd` directly (`mkLogRatNear` + `isNear_log_sfrac`); for `pn < pd` it
certifies the reciprocal `pd/pn > 1` and flips the sign with `isNear_log_inv` (`sfrac_recip`
witness), giving a `true`-signed enclosure. -/
meta def mkLogNearOf (pn pd D E : ℕ) : MetaM RNear := do
  if pn ≥ pd then
    let base ← mkLogRatNear pn pd D E
    let proof := mkAppN (mkConst ``isNear_log_sfrac)
      #[natLitShared pn, natLitShared pd, natLitShared base.cn, natLitShared base.cd,
        natLitShared base.rn,
        natLitShared base.rd, toExpr base.neg, base.proof]
    return { base with proof, x := mkRealFn ``Real.log (mkSfracR false pn pd) }
  else
    let recipCert ← mkLogRatNear pd pn D E
    -- `recipCert` encloses `Real.log (↑pd/↑pn)`, so the reciprocal-lemma argument `Q = ↑pd/↑pn`
    -- is built directly (matching `mkLogRatNear`'s `Real.log (mkCastDivR pd pn)` conclusion).
    let Q := mkCastDivR pd pn
    let Psfrac := mkSfracR false pn pd
    let hPQ := mkApp2 (mkConst ``sfrac_recip) (natLitShared pn) (natLitShared pd)
    let proof := mkAppN (mkConst ``isNear_log_inv)
      #[Psfrac, Q, natLitShared recipCert.cn, natLitShared recipCert.cd, natLitShared recipCert.rn,
        natLitShared recipCert.rd, hPQ, recipCert.proof]
    return { recipCert with proof, neg := true, x := mkRealFn ``Real.log Psfrac }

/-- Smallest-precision `log(sfrac false pn pd)` enclosure whose interval satisfies `fits`. Starts at
`2^k` (the caller seeds `k` from `eps`) and sharpens in 6-bit steps while `fuel` lasts. When the
fuel runs out, `refuted` (the enclosure lies entirely outside the target window) distinguishes a
false claim from a marginal one. -/
meta partial def mkLogNearFit (pn pd : ℕ) (fits refuted : RNear
      → Bool) (k fuel : ℕ) : MetaM RNear := do
  let c ← mkLogNearOf pn pd (2 ^ k) (2 ^ k)
  if fits c then return c
  else if fuel == 0 then
    if refuted c then throwError "log_check: the claim is false"
    else throwError
      "log_check: cannot resolve the claim at precision 1/2^{k}; it is marginal\
      \n(the target sits within the enclosure's margin of the true value; state the target to\
      \nmore digits, or use a larger eps)"
  else mkLogNearFit pn pd fits refuted (k + 6) (fuel - 1)

open Lean Elab Tactic Term Meta in
/-- `log_check` closes a goal `|Real.log p − x| < eps` where `p`, `x`, `eps` are rational literals
in any surface form (`p > 0`, `eps > 0`), all read by `recognizeRat`. `log p` is certified by
`mkLogNearOf` (canonical `sfrac` form: `p ≥ 1` directly, `p < 1` via the reciprocal and
`isNear_log_inv`), transported onto the goal's `p` by `isNear_log_arg`, and compared against
`x`/`eps` by `log_verify_gen` (two `reflBoolTrue` `Nat.blt` conditions). The internal precision
adapts to `eps`; errors if the claim is false, or marginal at the attempted precision. -/
elab "log_check" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr LT.lt _ _ lhs epsE := ty
    | throwError "log_check: goal must be `|Real.log p - x| < eps`"
  let_expr HSub.hSub _ _ _ _ e xE := lhs.appArg!
    | throwError "log_check: expected `|Real.log p - x|`"
  let_expr Real.log pE := e | throwError "log_check: expected `Real.log _`"
  let (pneg, pn, pd, ppf) ← recognizeRat pE
  if pneg then throwError "log_check: the argument p must be positive"
  let (xneg, xn, xd, xpf) ← recognizeRat xE
  let (eneg, en, ed, epf) ← recognizeRat epsE
  if eneg then throwError "log_check: eps must be positive"
  -- Signed interval containment `[±cn/cd ± rn/rd] ⊂ (±xn/xd ± en/ed)` via numPos/numNeg. The
  -- enclosure sign `cneg` is fixed by `pn < pd` (independent of precision), so the test is a pure
  -- predicate on the enclosure fields, used to drive the adaptive-precision search.
  let xp := if xneg then 0 else xn
  let xm := if xneg then xn else 0
  let fits : RNear → Bool := fun c =>
    let cp := if c.neg then 0 else c.cn
    let cm := if c.neg then c.cn else 0
    let cd := c.cd; let rn := c.rn; let rd := c.rd
    Nat.blt (xp * (ed * cd * rd) + cm * (xd * ed * rd) + rn * (cd * xd * ed))
            (cp * (xd * ed * rd) + xm * (ed * cd * rd) + en * (xd * cd * rd)) &&
    Nat.blt (cp * (xd * ed * rd) + xm * (ed * cd * rd) + rn * (cd * xd * ed))
            (xp * (ed * cd * rd) + cm * (xd * ed * rd) + en * (xd * cd * rd))
  -- The claim is PROVABLY false when the enclosure `[c−r, c+r]` lies entirely outside the target
  -- window `(x−eps, x+eps)` (then `|log p − x| ≥ |c−x| − r ≥ eps`); used only to pick the right
  -- error message at the precision cap, so plain `ℕ` arithmetic, nothing kernel-checked.
  let refuted : RNear → Bool := fun c =>
    let cp := if c.neg then 0 else c.cn
    let cm := if c.neg then c.cn else 0
    let cd := c.cd; let rn := c.rn; let rd := c.rd
    Nat.ble (cm*(rd*xd*ed) + rn*(cd*xd*ed) + xp*(cd*rd*ed) + en*(cd*rd*xd))
            (cp*(rd*xd*ed) + xm*(cd*rd*ed)) ||
    Nat.ble (cp*(rd*xd*ed) + rn*(cd*xd*ed) + xm*(cd*rd*ed) + en*(cd*rd*xd))
            (xp*(cd*rd*ed) + cm*(rd*xd*ed))
  -- Certify `log(sfrac false pn pd)` (signed for `pn/pd < 1`) to the smallest precision that fits,
  -- starting a few bits below `1/eps` (`eps = en/ed`, so `⌊log₂(ed/en)⌋` bits reach `eps`).
  let cert0 ← mkLogNearFit pn pd fits refuted (Nat.log2 (ed / en + 1) + 3) 5
  let cneg := cert0.neg
  let cn := cert0.cn; let cd := cert0.cd; let rn := cert0.rn; let rd := cert0.rd
  -- Transport the canonical enclosure onto the goal's opaque argument `pE` via `ppf`.
  let cert := mkAppN (mkConst ``isNear_log_arg)
    #[pE, natLitShared pn, natLitShared pd, natLitShared cn, natLitShared cd, natLitShared rn,
      natLitShared rd,
      toExpr cneg, ppf, cert0.proof]
  let pf := mkAppN (mkConst ``log_verify_gen)
    #[pE, xE, epsE, toExpr cneg, toExpr xneg, natLitShared cn, natLitShared cd, natLitShared rn,
      natLitShared rd,
      natLitShared xn, natLitShared xd, natLitShared en, natLitShared ed, cert, xpf, epf,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  -- Assign the certificate by raw `MVarId.assign` (quickRfl-style), leaving the single defeq
  -- check of `pf`'s type against the goal to the kernel.
  liftMetaFinishingTactic (·.assign pf)

/-! ### Monotone images: `log` and the reciprocal of an enclosure

`sin`/`cos` images go through the centre (1-Lipschitz); `log` and `x⁻¹` have no global Lipschitz
constant, so their images go through the interval's exact rational endpoints instead: certify (or
compute exactly, for the reciprocal) the function at both endpoints and sandwich by
monotonicity. -/

/-- The shared `π` enclosure as an `RNear`: a named tier for `D ≤ 10⁵⁰`, else a fresh Machin
build. -/
meta def mkPiNear (D : ℕ) : MetaM RNear := do
  let (E, P, Q, proof) ← match ← mkPiTier? D with
    | some r => pure r
    | none => do
      let (P, Q, pf) ← mkPiProof D
      pure (D, P, Q, pf)
  return { proof, x := mkPiE, neg := false, cn := P, cd := Q, rn := 1, rd := E }

/-- Reciprocal of an enclosure with strictly positive lower endpoint: `x⁻¹ ∈ [a/Q, b/Q]` where
`a/Q ≤ 1/hi` and `1/lo ≤ b/Q` at the dyadic `Q` (the endpoints of `x⁻¹` are exact rationals, so
no certificate is involved), via `Real.IsNear.inv_image`. -/
meta def mkInvImageNear (S : RNear) (D : ℕ) : MetaM RNear := do
  if S.neg then throwError "mkInvImageNear: negative centre not supported"
  unless S.rn * S.cd < S.cn * S.rd do
    throwError "mkInvImageNear: the enclosure must be strictly positive"
  let Q := dyadicDenom D
  let den := S.cd * S.rd
  let lon := S.cn * S.rd - S.rn * S.cd
  let hin := S.cn * S.rd + S.rn * S.cd
  let a := (Q * den) / hin
  let b := (Q * den + lon - 1) / lon
  let proof := mkAppN (mkConst ``Real.IsNear.inv_image)
    #[S.x, natLitShared S.cn, natLitShared S.cd, natLitShared S.rn, natLitShared S.rd,
      natLitShared a, natLitShared b, natLitShared Q, S.proof, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  litNear { proof, x := mkInvR S.x, neg := false, cn := a + b, cd := 2 * Q, rn := b - a,
            rd := 2 * Q }

/-- `log` of an enclosure with strictly positive lower endpoint: certify `log` at the exact
rational endpoints (`mkLogNearOf` at `1/(2D)`, so any positive rationals work, range-reduced as
needed), then cover the sandwich with dyadic literal result fields through `isNear_log_image`.
The centre is the rounded midpoint of the two endpoint values, the radius the rounded-up
half-width. -/
meta def mkLogImageNear (S : RNear) (D : ℕ) : MetaM RNear := do
  if S.neg then throwError "mkLogImageNear: negative centre not supported"
  unless S.rn * S.cd < S.cn * S.rd do
    throwError "mkLogImageNear: the enclosure must be strictly positive"
  let den := S.cd * S.rd
  let lon := S.cn * S.rd - S.rn * S.cd
  let hin := S.cn * S.rd + S.rn * S.cd
  let g1 := Nat.gcd lon den
  let L1 := lon / g1
  let K1 := den / g1
  let g2 := Nat.gcd hin den
  let L2 := hin / g2
  let K2 := den / g2
  let h1 ← mkLogNearOf L1 K1 (2 * D) (2 * D)
  let h2 ← mkLogNearOf L2 K2 (2 * D) (2 * D)
  let q1 : ℚ := (if h1.neg then -1 else 1) * (h1.cn : ℚ) / h1.cd - (h1.rn : ℚ) / h1.rd
  let q2 : ℚ := (if h2.neg then -1 else 1) * (h2.cn : ℚ) / h2.cd + (h2.rn : ℚ) / h2.rd
  let Q := dyadicDenom D
  let cZ : ℤ := ((q1 + q2) / 2 * Q).floor
  let nR := decide (cZ < 0)
  let cnR := cZ.natAbs
  let cQ : ℚ := (cZ : ℚ) / (Q : ℚ)
  let rnR := ((max (cQ - q1) (q2 - cQ)) * Q).ceil.toNat
  -- sign-specialized variants (numPos-free hL/hH); impossible combinations fall back
  let variant : Option Name := match h1.neg, h2.neg, nR with
    | false, false, false => some ``isNear_log_image_fff
    | true,  true,  true  => some ``isNear_log_image_ttt
    | true,  false, false => some ``isNear_log_image_tff
    | true,  false, true  => some ``isNear_log_image_tft
    | _,     _,     _     => none
  let boolArgs : Array Expr := if variant.isSome then #[]
    else #[toExpr h1.neg, toExpr h2.neg, toExpr nR]
  let proof := mkAppN (mkConst (variant.getD ``isNear_log_image))
    (#[S.x] ++ boolArgs ++
    #[natLitShared S.cn, natLitShared S.cd, natLitShared S.rn, natLitShared S.rd,
      natLitShared L1, natLitShared K1, natLitShared L2, natLitShared K2,
      natLitShared h1.cn, natLitShared h1.cd, natLitShared h1.rn, natLitShared h1.rd,
      natLitShared h2.cn, natLitShared h2.cd, natLitShared h2.rn, natLitShared h2.rd,
      natLitShared cnR, natLitShared Q, natLitShared rnR, natLitShared Q,
      S.proof, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, h1.proof, h2.proof,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue])
  litNear { proof, x := mkRealFn ``Real.log S.x, neg := nR, cn := cnR, cd := Q, rn := rnR, rd := Q }

open Elab Term in
/-- `logPi_near% D` : an enclosure of `Real.log π`, i.e. `log` of the `π`-tier enclosure. -/
elab "logPi_near% " Dn:num : term => do
  return (← mkLogImageNear (← mkPiNear Dn.getNat) Dn.getNat).proof

open Elab Term in
/-- `invPi_near% D` : an enclosure of `π⁻¹`, i.e. the reciprocal image of the `π`-tier
enclosure. -/
elab "invPi_near% " Dn:num : term => do
  return (← mkInvImageNear (← mkPiNear Dn.getNat) Dn.getNat).proof

/-! ### `arctan` of any positive rational

The alternating certificate covers `u/v < 1` directly. Larger arguments go through the
complementary angle: `arctan(u/v) = π/2 − arctan(v/u)` (`arctan_recip`), with the `π/2` piece a
shared named `π` tier scaled by the exact constant `1/2`, and the diagonal `u = v` the exact
quarter turn (`arctan_diag`). This is what a `Complex.log` imaginary part needs, where the
component ratio `im/re` is any positive rational. -/

/-- Enclose `Real.arctan (u/v)` for a positive fraction in the certificate range (`u < v`),
through `mkSignedCertNear` (the alternating even/odd certificate from `mkArctanPos`). -/
meta def mkArctanNear (u v D : ℕ) : MetaM RNear := mkSignedCertNear mkArctanPos ``Real.arctan u v D

/-- Enclose `sfrac false num den * π`: a shared named `π` tier (fresh Machin build above the
`1/10⁵⁰` tier) scaled by the exact rational constant. Radius `num/(den·E)` with `E ≥ D`. -/
meta def mkPiScaledNear (num den D : ℕ) : MetaM RNear := do
  let (E, P, Q, proof) ← match ← mkPiTier? D with
    | some r => pure r
    | none => do
      let (P, Q, pf) ← mkPiProof D
      pure (D, P, Q, pf)
  mulNear (← mkConstNear num den) { proof, x := mkPiE, neg := false, cn := P, cd := Q,
                                    rn := 1, rd := E }

/-- Enclose `Real.arctan (u/v)` for any positive rational, radius at most `1/D`. In range
(`u < v`) this is the direct certificate; on the diagonal (`u = v`) the exact `π/4`; out of range
(`u > v`) the complementary angle `π/2 − arctan(v/u)`, both pieces at `1/(2D)` or better. -/
meta def mkArctanNearGen (u v D : ℕ) : MetaM RNear := do
  if u < v then
    mkArctanNear u v D
  else if v == 0 then
    throwError "mkArctanNearGen: the argument u/v needs v > 0"
  else if u == v then
    let quarter ← mkPiScaledNear 1 4 D
    let he := mkAppN (mkConst ``arctan_diag)
      #[natLitShared u, natLitShared v, reflBoolTrue, reflBoolTrue]
    ofEqNear (mkRealFn ``Real.arctan (mkCastDivR u v)) he quarter
  else
    let inner ← mkArctanNear v u (2 * D)
    let halfPi ← mkPiScaledNear 1 2 (2 * D)
    let he := mkAppN (mkConst ``arctan_recip)
      #[natLitShared u, natLitShared v, reflBoolTrue, reflBoolTrue]
    ofEqNear (mkRealFn ``Real.arctan (mkCastDivR u v)) he (← subNear halfPi inner)

open Elab Term in
/-- `arctanGen_near% u v D` : an enclosure of `Real.arctan (u/v)` for any positive rational,
range-reduced as needed. -/
elab "arctanGen_near% " un:num vn:num Dn:num : term => do
  return (← mkArctanNearGen un.getNat vn.getNat Dn.getNat).proof

/-! ### The complex logarithm

For `z = (p + r·i)/q` in the right half-plane (`p, q > 0`, `r ≥ 0`), both components of
`Complex.log z` are certified real values at exact rationals: `(log z).re = ½·log((p²+r²)/q²)`
(`clog_re_eq`) and `(log z).im = arctan(r/p)` (`clog_im_eq`), each transported onto the
projection by `ofEqNear`. The rectangle is the componentwise pair of these two enclosures. -/

/-- Rectangle enclosure of `Complex.log ⟨p/q, r/q⟩` (`p, q > 0`), each component with radius
about `1/D`: real part `½·log(normSq)` via `mkLogNearOf` and the constant `1/2`, imaginary part
`arctan(r/p)` via `mkArctanNearGen` (range-reduced whenever `r ≥ p`). -/
meta def cLogNear (p r q D : ℕ) : MetaM CNear := do
  let N := p * p + r * r
  let M := q * q
  let logNM ← mkLogNearOf N M (2 * D) (2 * D)
  let reRaw ← mulNear (← mkConstNear 1 2) logNM
  let heRe := mkAppN (mkConst ``clog_re_eq)
    #[natLitShared p, natLitShared r, natLitShared q, natLitShared N, natLitShared M,
      reflBoolTrue, reflBoolTrue, reflBoolTrue]
  let heIm := mkAppN (mkConst ``clog_im_eq)
    #[natLitShared p, natLitShared r, natLitShared q, reflBoolTrue, reflBoolTrue]
  let zlog := mkClogZE p r q
  return { re := ← ofEqNear (mkApp (mkConst ``Complex.re) zlog) heRe reRaw,
           im := ← ofEqNear (mkApp (mkConst ``Complex.im) zlog) heIm (← mkArctanNearGen r p D) }

open Elab Term in
/-- `clog_near% p r q D` : the rectangle enclosure of `Complex.log ((p + r·i)/q)`, concluded
about the named value through `Complex.IsNear.of_parts`. -/
elab "clog_near% " pn:num rn:num qn:num Dn:num : term => do
  let c ← cLogNear pn.getNat rn.getNat qn.getNat Dn.getNat
  let zlog := c.re.x.appArg!
  return mkAppN (mkConst ``Complex.IsNear.of_parts)
    #[zlog, toExpr c.re.neg, natLitShared c.re.cn, natLitShared c.re.cd, natLitShared c.re.rn,
      natLitShared c.re.rd, toExpr c.im.neg, natLitShared c.im.cn, natLitShared c.im.cd,
      natLitShared c.im.rn, natLitShared c.im.rd, c.re.proof, c.im.proof]

/-! ### Composite-enclosure `_near%` elaborators

The interactive surface for building one small certified computation at a time (a single function,
a composite, or a finite `∑ exp`) on top of the combinators above. The `*_near%` defs below are
worked examples exercising each. -/

open Elab Term in
/-- `expMul_near% a b D` : an enclosure of `Real.exp a · Real.exp b` assembled by `mulNear` from two
`exp` enclosures. Exercises the builder and meta combinator end-to-end. -/
elab "expMul_near% " an:num bn:num Dn:num : term => do
  let r ← mulNear (← mkExpNear an.getNat 1 Dn.getNat) (← mkExpNear bn.getNat 1 Dn.getNat)
  return r.proof

open Elab Term in
/-- `expAdd_near% a b D` : an enclosure of `Real.exp a + Real.exp b` via `addNear`. Exercises the
builder path that pins the result sign/magnitude and discharges `hnum` by `reflBoolTrue`. -/
elab "expAdd_near% " an:num bn:num Dn:num : term => do
  let r ← addNear (← mkExpNear an.getNat 1 Dn.getNat) (← mkExpNear bn.getNat 1 Dn.getNat)
  return r.proof

open Elab Term in
/-- `sin_near% u D` : an enclosure of `Real.sin u` (validates the signed ingestion path). -/
elab "sin_near% " un:num Dn:num : term => do
  return (← mkSinNear un.getNat 1 Dn.getNat).proof

open Elab Term in
/-- `sinExp_near% a b D` : an enclosure of `Real.sin a · Real.exp b` (cross-function `mulNear`). -/
elab "sinExp_near% " an:num bn:num Dn:num : term => do
  let r ← mulNear (← mkSinNear an.getNat 1 Dn.getNat) (← mkExpNear bn.getNat 1 Dn.getNat)
  return r.proof

open Elab Term in
/-- `sinFrac_near% u v D` : an enclosure of `sin (u/v)` via the `v ≥ 2` certificate path. -/
elab "sinFrac_near% " un:num vn:num Dn:num : term => do
  return (← mkSinNear un.getNat vn.getNat Dn.getNat).proof

open Elab Term in
/-- `sinSin_near% u D` : an enclosure of `sin (sin u)`, i.e. `sin` of the enclosure `sin u`.
Exercises the Lipschitz image builder `mkSinImageNear` (sin of an irrational argument). -/
elab "sinSin_near% " un:num Dn:num : term => do
  let a ← mkSinNear un.getNat 1 Dn.getNat
  return (← mkSinImageNear a Dn.getNat).proof

open Elab Term in
/-- `cosSin_near% u D` : an enclosure of `cos (sin u)`, i.e. `cos` of the enclosure `sin u`. -/
elab "cosSin_near% " un:num Dn:num : term => do
  let a ← mkSinNear un.getNat 1 Dn.getNat
  return (← mkCosImageNear a Dn.getNat).proof

open Elab Term in
/-- `log_near% n D` : an enclosure of `Real.log n` (odd `n ≤ 5`). -/
elab "log_near% " nn:num Dn:num : term => do
  return (← mkLogNear nn.getNat Dn.getNat).proof

open Elab Term in
/-- `logred_near% n D E` : an enclosure of `Real.log (n/1)` via range reduction (any `n ≥ 1`). -/
elab "logred_near% " nn:num Dn:num En:num : term => do
  return (← mkLogRatReduceNear nn.getNat 1 Dn.getNat En.getNat).proof

open Elab Term in
/-- `sqrt_near% N M D` : an enclosure of `√(N/M)` as an `RNear` (midpoint ± half-width). -/
elab "sqrt_near% " Nn:num Mn:num Dn:num : term => do
  return (← mkSqrtNear Nn.getNat Mn.getNat Dn.getNat).proof

open Elab Term in
/-- `cabs_near% re im D` : an enclosure of `|re + im·i|` via `cAbsNear`. -/
elab "cabs_near% " ren:num imn:num Dn:num : term => do
  let z : CNear := { re := ← mkConstNear ren.getNat 1, im := ← mkConstNear imn.getNat 1 }
  return (← cAbsNear z Dn.getNat).proof

open Elab Term in
/-- `deepMul_near% b D k` : `exp b` enclosed, then squared `k` times via `mulNear`, i.e. an
enclosure of `(exp b)^(2^k)`. Exercises `renorm`'s capping branch (`Real.IsNear.recentre`). -/
elab "deepMul_near% " bn:num Dn:num kn:num : term => do
  let mut r ← mkExpNear bn.getNat 1 Dn.getNat
  for _ in [0:kn.getNat] do
    r ← mulNear r r
  return r.proof

open Elab Term in
/-- `cmulAbs_near% ar ai br bi D` : `|(ar + ai·i)·(br + bi·i)|`, assembled by `cmulNear` (complex
rectangle multiply) then `cAbsNear`. Exercises the complex combinator layer end-to-end. -/
elab "cmulAbs_near% " arn:num ain:num brn:num bin:num Dn:num : term => do
  let za : CNear := { re := ← mkConstNear arn.getNat 1, im := ← mkConstNear ain.getNat 1 }
  let zb : CNear := { re := ← mkConstNear brn.getNat 1, im := ← mkConstNear bin.getNat 1 }
  return (← cAbsNear (← cmulNear za zb) Dn.getNat).proof

open Elab Term in
/-- `finsetSumExp_near% D S` : an enclosure of `∑ i ∈ S, Real.exp i` (precision `1/D`) for a
`Finset` `S` written as `Finset.range n` or `Finset.Ico a b` with numeral bounds, recognised at the
syntax level (no elaboration) and summed by `mkFinsetSumNear` (binary recursion + `addNear`, each
term a genuine `exp` enclosure). -/
elab "finsetSumExp_near% " Dn:num Sn:term : term => do
  let inner : Term ← match Sn with
    | `(($t)) => pure t
    | t => pure t
  let shape ← match inner with
    | `(Finset.range $n:num) => pure (FinsetShape.range n.getNat)
    | `(Finset.Ico $a:num $b:num) => pure (FinsetShape.ico a.getNat b.getNat)
    | _ => throwError "finsetSumExp_near%: expected `Finset.range n` or `Finset.Ico a b` (numerals)"
  let f := Expr.lam `i (mkConst ``Nat)
    (mkApp (mkConst ``Real.exp) (mkApp3 (mkConst ``Nat.cast [.zero]) (mkConst ``Real)
      (mkConst ``Real.instNatCast) (.bvar 0))) .default
  return (← mkFinsetSumNear (fun i => mkExpNear i 1 Dn.getNat) f shape).proof

end BSN
