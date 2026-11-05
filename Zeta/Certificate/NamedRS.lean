module

public import Zeta.Certificate.Bernoulli
public import Zeta.Certificate.HardyZDefs
public import Zeta.Certificate.Cpow
public import Zeta.Certificate.HardyZ
public import Zeta.Certificate.Named

/-!
# Named rectangle enclosures

Threads *named* values (`zetaApproximant …`, `(ascPochhammer ℂ m).eval s`, …) through the
rectangle arithmetic:

- a `CNamed` is a rectangle proof `Complex.IsNear z …` for an explicit `z`, with the components
  recovered as `And` projections;
- `cAddNamed`/`cSubNamed`/`cMulNamed` combine components and pass through
  `Complex.IsNear.add/sub/mul`, naming the result `z + w`/`z - w`/`z * w`;
- `cnamedOfEq` renames along a proven equality (a leaf or step identity).

Interval arithmetic carries all values; the equalities only ever rename.
-/
@[expose] public section


namespace BSN
open Enclosure

open Complex Complex.Stirling

open Lean Meta

/-! ### The Riemann-Siegel Hardy `Z` approximants -/

/-- The Riemann–Siegel cutoff `N = ⌊√(t/2π)⌋₊` for the endpoint `t = tn/td`, in exact ℕ arithmetic
against the same rational π bounds `floor_sqrt_eq_dec` proves with
(`2π·10²⁰ ∈ (628318530717958647692, 628318530717958647694)`). `none` iff `t` lies within
`~2k²·10⁻²⁰` of a `2πk²` boundary, too close to be decided at that precision. -/
meta def cutoffRS? (tn td : Nat) : Option Nat :=
  let k := Nat.sqrt (100000000000000000000 * tn / (628318530717958647694 * td))
  [k, k + 1].find? fun n ↦
    Nat.ble (628318530717958647694 * (n * n) * td) (100000000000000000000 * tn) &&
      Nat.blt (100000000000000000000 * tn) (628318530717958647692 * ((n + 1) * (n + 1)) * td)

/-- Reciprocal of an enclosure of either sign: `mkInvImageNear` supports only a positive centre,
so a negative one is inverted through `x⁻¹ = -((-x)⁻¹)`. -/
meta def mkInvSignedNear (S : RNear) (D : ℕ) : MetaM RNear := do
  if S.neg then
    let inv ← negNear (← mkInvImageNear (← negNear S) D)
    let he := mkApp (mkConst ``inv_eq_neg_inv_neg) S.x
    ofEqNearHe (← lemmaLhs he) he inv
  else
    mkInvImageNear S D

/-- `(√n)⁻¹` to `1/D`, sealed as an aux lemma once per `(n, D)` so the kernel checks it once per
module rather than once per endpoint. Memoized per process (`invSqrtNatCache`), guarded by
`proofsInEnv`. -/
meta def mkInvSqrtNatSealed (n D : ℕ) : MetaM RNear := do
  if let some r := (← invSqrtNatCache.get)[(n, D)]? then
    if ← proofsInEnv #[r.proof] then return r
  let r ← cachedNear do mkInvImageNear (← mkSqrtNatNear n D) D
  invSqrtNatCache.modify (·.insert (n, D) r)
  return r

/-- Round an enclosure onto exactly `·/B`: the centre floored, the radius ceiled to absorb the drop,
both denominators `B` (no `gcd` reduction, unlike `roundFieldsAt`), through `Real.IsNear.recentre`.
Puts every input of `mainSumRS_step` on its shared denominator. -/
meta def recentreExactNear (r : RNear) (B : ℕ) : MetaM RNear := do
  if r.cd == B && r.rd == B then return r
  let cnF := (r.cn * B) / r.cd
  let cnErr := r.cn * B - cnF * r.cd
  let num := r.rn * (r.cd * B) + cnErr * r.rd
  let den := r.rd * (r.cd * B)
  mkRecentreNear r cnF B ((num * B + den - 1) / den) B

/-- The main sum's shared denominator `B` at working precision `D`: `2^-bits` with three bits of
headroom over the trig-argument grid, so rounding onto it costs no measurable radius. -/
meta def mainSumDenom (D : ℕ) : ℕ := 2 ^ ((2 * D).log2 + argRecentreGuard + 3)

/-- `π` on its own grid `M = B·2²⁴` (its error is multiplied by `k ≲ 2²²` at height `10⁶`), sealed
once per module. -/
meta def mkPiNearMain (B : ℕ) : MetaM RNear := do
  let M := B * 2 ^ 24
  sealedConst "π main sum" M do
    let some (E, P, Q, pf) ← mkPiTier? M
      | throwError "mkPiNearMain: precision {M} is beyond the 10⁵⁰ π tier"
    let π₀ : RNear := { proof := pf, x := mkPiE, neg := false, cn := P, cd := Q, rn := 1, rd := E }
    recentreExactNear π₀ M

/-- One main-sum step through `mainSumRS_step`: from the enclosure `S` of `mainSumRS θ t (b-1)`,
the phase `θ`, the sealed `log b`/`(√b)⁻¹` and the `π` enclosure `πM`, all on the shared denominator
`B` (`πM` on `M`), build the enclosure of `mainSumRS θ t b` on `B`.

The meta side reduces the exact phase centre `φc = (td·θc − tn·Lc)/(td·B)` itself: `k =
⌊|φc|/(π/2)⌋` at `πM`, the remainder floored onto `·/B` as `u/B`, and the in-range `cos`/`sin`
certificate of `u/B` (`k mod 4` picks which, and the sign) at `1/DI = 2/B`, whose dyadic
denominator is then `B` itself. The new centre is floored onto `·/B` and the radius rounded up onto
it. Every numeral condition holds by construction, so the checks are `reflBoolTrue`. -/
meta def mainSumStepNear (S θ logN invS πM : RNear) (tE htE : Expr) (tn td b B : ℕ) :
    MetaM RNear := do
  let sgn (neg : Bool) (n : ℕ) : Int := if neg then -(n : Int) else n
  let (M, Pc, rπ, DI) := (πM.cd, πM.cn, πM.rn, B / 2)
  -- the phase centre `(td·θc − tn·Lc)/(td·B)`, exact, as `±N/(td·B)`
  let num : Int := sgn θ.neg θ.cn * (td : Int) - ((tn * logN.cn : ℕ) : Int)
  let nφ := decide (num < 0)
  let N := num.natAbs
  let k := 2 * M * N / (td * B * Pc)
  let u := (2 * M * N - k * Pc * td * B) / (2 * M * td)
  let j := k % 4
  let (pI, nI, cI, Q) ← if j % 2 == 0 then mkCosPos u B DI else mkSinPos u B DI
  unless Q == B do throwError "mainSumStepNear: certificate denominator {Q} is not B = {B}"
  let flip := j == 1 || j == 2
  let nC := if flip then !nI else nI
  let (εE, hε, hsign) := if flip
    then (``quadSignNeg, ``abs_quadSignNeg, ``sfrac_not_eq_quadSignNeg_mul)
    else (``quadSignPos, ``abs_quadSignPos, ``sfrac_eq_quadSignPos_mul)
  let hquad := #[``cos_quad_nat0, ``cos_quad_nat1, ``cos_quad_nat2, ``cos_quad_nat3][j]!
  let gE := mkConst (if j % 2 == 0 then ``Real.cos else ``Real.sin)
  -- the new centre `(Sc·B + Ac·Cc)/B²`, floored onto `·/B`
  let numX : Int := sgn S.neg S.cn * (B : Int) + (invS.cn : Int) * sgn nC cI
  let cRi := Int.fdiv numX B
  -- the radius, rounded up onto `·/B`
  let radNum := (S.rn + invS.rn + 1) * B * td * (2 * M)
    + invS.cn * (2 * M * (td * (θ.rn + 3) + tn * logN.rn) + k * rπ * (td * B))
  let radDen := B * td * (2 * M)
  let rR := (radNum + radDen - 1) / radDen
  let proof := mkAppN (mkConst ``mainSumRS_step)
    #[θ.x, tE, gE, mkConst εE, natLitShared (b - 1), natLitShared b, natLitShared tn,
      natLitShared td, natLitShared k, natLitShared B, natLitShared DI, natLitShared M,
      toExpr θ.neg, natLitShared θ.cn, natLitShared θ.rn, natLitShared logN.cn,
      natLitShared logN.rn, natLitShared invS.cn, natLitShared invS.rn, toExpr S.neg,
      natLitShared S.cn, natLitShared S.rn, toExpr nφ, natLitShared u, natLitShared Pc,
      natLitShared rπ, toExpr nI, natLitShared cI, toExpr nC, toExpr (decide (cRi < 0)),
      natLitShared cRi.natAbs, natLitShared rR,
      mkConst hε, mkApp2 (mkConst hquad) (natLitShared k) reflBoolTrue,
      mkApp3 (mkConst hsign) (toExpr nI) (natLitShared cI) (natLitShared B),
      htE, reflBoolTrue, S.proof, θ.proof, logN.proof, invS.proof, πM.proof, pI,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return { proof, x := mkApp3 (mkConst ``mainSumRS) θ.x tE (natLitShared b),
           neg := decide (cRi < 0), cn := cRi.natAbs, cd := B, rn := rR, rd := B }

/-- The per-term choices of a main-sum step: the phase reduction (`nφ`, `k`, `u`), the in-range
certificate (`pI`, `nI`, `cI`) and the quadrant's sign lemmas. Shared by the single and paired
steps. -/
meta structure MainSumTerm where
  nφ : Bool
  k : ℕ
  u : ℕ
  pI : Expr
  nI : Bool
  cI : ℕ
  nC : Bool
  εE : Name
  hε : Name
  hsign : Name
  hquad : Name
  gE : Expr

/-- The per-term part of `mainSumStepNear` for the term with log enclosure `L`: reduce the phase
centre `(td·θc − tn·Lc)/(td·B)` by `k·π/2` at `πM`, floor the remainder onto `·/B` as `u/B`, and
build the in-range `cos`/`sin` certificate of `u/B` at `1/DI = 2/B`. -/
meta def mainSumTermNear (θ L πM : RNear) (tn td B : ℕ) : MetaM MainSumTerm := do
  let sgn (neg : Bool) (n : ℕ) : Int := if neg then -(n : Int) else n
  let (M, Pc, DI) := (πM.cd, πM.cn, B / 2)
  let num : Int := sgn θ.neg θ.cn * (td : Int) - ((tn * L.cn : ℕ) : Int)
  let N := num.natAbs
  let k := 2 * M * N / (td * B * Pc)
  let u := (2 * M * N - k * Pc * td * B) / (2 * M * td)
  let j := k % 4
  let (pI, nI, cI, Q) ← if j % 2 == 0 then mkCosPos u B DI else mkSinPos u B DI
  unless Q == B do throwError "mainSumTermNear: certificate denominator {Q} is not B = {B}"
  let flip := j == 1 || j == 2
  let (εE, hε, hsign) := if flip
    then (``quadSignNeg, ``abs_quadSignNeg, ``sfrac_not_eq_quadSignNeg_mul)
    else (``quadSignPos, ``abs_quadSignPos, ``sfrac_eq_quadSignPos_mul)
  return { nφ := decide (num < 0), k, u, pI, nI, cI, nC := if flip then !nI else nI, εE, hε, hsign,
           hquad := #[``cos_quad_nat0, ``cos_quad_nat1, ``cos_quad_nat2, ``cos_quad_nat3][j]!,
           gE := mkConst (if j % 2 == 0 then ``Real.cos else ``Real.sin) }

/-- Two main-sum steps at once through `mainSumRS_step2`: from `S` enclosing `mainSumRS θ t (b₁-1)`,
enclose `mainSumRS θ t (b₁+1)`, with one floored centre and one radius check for the pair. -/
meta def mainSumPairNear (S θ L₁ A₁ L₂ A₂ πM : RNear) (tE htE : Expr) (tn td b₁ B : ℕ) :
    MetaM RNear := do
  let sgn (neg : Bool) (n : ℕ) : Int := if neg then -(n : Int) else n
  let (M, Pc, rπ, DI) := (πM.cd, πM.cn, πM.rn, B / 2)
  let d₁ ← mainSumTermNear θ L₁ πM tn td B
  let d₂ ← mainSumTermNear θ L₂ πM tn td B
  -- the new centre `(Sc·B + A₁c·C₁c + A₂c·C₂c)/B²`, floored onto `·/B`
  let numX : Int := sgn S.neg S.cn * (B : Int) + (A₁.cn : Int) * sgn d₁.nC d₁.cI
    + (A₂.cn : Int) * sgn d₂.nC d₂.cI
  let cRi := Int.fdiv numX B
  -- the radius of both terms, rounded up onto `·/B`
  let radNum := (S.rn + A₁.rn + A₂.rn + 1) * B * td * (2 * M)
    + A₁.cn * (2 * M * (td * (θ.rn + 3) + tn * L₁.rn) + d₁.k * rπ * (td * B))
    + A₂.cn * (2 * M * (td * (θ.rn + 3) + tn * L₂.rn) + d₂.k * rπ * (td * B))
  let radDen := B * td * (2 * M)
  let rR := (radNum + radDen - 1) / radDen
  let lit := natLitShared
  let proof := mkAppN (mkConst ``mainSumRS_step2)
    #[θ.x, tE, d₁.gE, d₂.gE, mkConst d₁.εE, mkConst d₂.εE, lit (b₁ - 1), lit b₁, lit (b₁ + 1),
      lit tn, lit td, lit d₁.k, lit d₂.k, lit B, lit DI, lit M,
      toExpr θ.neg, lit θ.cn, lit θ.rn, lit L₁.cn, lit L₁.rn, lit A₁.cn, lit A₁.rn,
      lit L₂.cn, lit L₂.rn, lit A₂.cn, lit A₂.rn, toExpr S.neg, lit S.cn, lit S.rn,
      toExpr d₁.nφ, lit d₁.u, toExpr d₂.nφ, lit d₂.u, lit Pc, lit rπ,
      toExpr d₁.nI, lit d₁.cI, toExpr d₁.nC, toExpr d₂.nI, lit d₂.cI, toExpr d₂.nC,
      toExpr (decide (cRi < 0)), lit cRi.natAbs, lit rR,
      mkConst d₁.hε, mkApp2 (mkConst d₁.hquad) (lit d₁.k) reflBoolTrue,
      mkApp3 (mkConst d₁.hsign) (toExpr d₁.nI) (lit d₁.cI) (lit B),
      mkConst d₂.hε, mkApp2 (mkConst d₂.hquad) (lit d₂.k) reflBoolTrue,
      mkApp3 (mkConst d₂.hsign) (toExpr d₂.nI) (lit d₂.cI) (lit B),
      htE, reflBoolTrue, reflBoolTrue, S.proof, θ.proof, L₁.proof, A₁.proof, L₂.proof, A₂.proof,
      πM.proof, d₁.pI, d₂.pI,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  return { proof, x := mkApp3 (mkConst ``mainSumRS) θ.x tE (lit (b₁ + 1)),
           neg := decide (cRi < 0), cn := cRi.natAbs, cd := B, rn := rR, rd := B }

/-- The named `riemannSiegelThetaApproximant 2 0 t` at `t = tn/td`, through the real closed form
`riemannSiegelThetaApproximant_two_zero_mk`: one real `log (1/16 + t²/4)`, one small
`arctan (1/(2t))`, the sealed `log π` and an exact rational tail, instead of the complex Stirling
evaluation. The two logs are multiplied by `t/4` and `t/2`, so they are taken at `8D`, which keeps
the radius well below the complex route's. Needs `t ≥ 1` (so `td < 2tn` and the tail's sign is
fixed), which every Riemann–Siegel endpoint (`t ≥ 32π`) satisfies. -/
meta def mkThetaNamedRS (tE htE : Expr) (tn td D : ℕ) : MetaM RNear := do
  unless td ≤ tn do throwError "mkThetaNamedRS: needs t ≥ 1, got {tn}/{td}"
  let S := td * td + 4 * tn * tn
  let (Q, V, T4, T2) := (16 * td * td, 2 * tn, 4 * td, 2 * td)
  let Rn := 30 * tn * td * S ^ 2 + 64 * tn ^ 3 * td ^ 3 - 48 * tn * td ^ 5
  let Rd := 45 * S ^ 3
  let L ← mkLogNearOf S Q (8 * D) (8 * D)
  let A ← mkArctanNear td V D
  let halfPi ← mulNear (← mkConstNear 1 2) (← mkPiNear D)
  let logPi ← sealedConst "log π" (8 * D) (mkLogImageNear (← mkPiNear (8 * D)) (8 * D))
  let e1 ← mulNear (← mkConstNear tn T4) L
  let e2 ← mulNear (← mkConstNear 1 4) (← subNear halfPi A)
  let e4 ← mulNear (← mkConstNear tn T2) logPi
  let rPf := mkAppN (mkConst ``Real.IsNear.const) #[toExpr true, natLitShared Rn, natLitShared Rd]
  let R : RNear :=
    { proof := rPf, x := mkSfracR true Rn Rd, neg := true, cn := Rn, cd := Rd, rn := 0, rd := 1 }
  let raw ← addNear (← subNear (← subNear (← subNear e1 e2) (← mkConstNear tn T2)) e4) R
  let he := mkAppN (mkConst ``riemannSiegelThetaApproximant_two_zero_mk)
    #[tE, natLitShared tn, natLitShared td, natLitShared S, natLitShared Q, natLitShared V,
      natLitShared T4, natLitShared T2, natLitShared Rn, natLitShared Rd, htE,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue]
  let lhs := mkAppN (mkConst ``riemannSiegelThetaApproximant) #[natLitShared 2, natLitShared 0, tE]
  ofEqNearHe lhs he raw

/-- `2π` and `(2π)⁻¹` at precision `D`, each sealed once per module (`sealedConst`). -/
meta def mkTwoPiSealed (D : ℕ) : MetaM (RNear × RNear) := do
  let piN ← sealedConst "π" D (mkPiNear D)
  let twoPi ← sealedConst "2π" D (mulNear (← mkConstNear 2 1) piN)
  let invTwoPi ← sealedConst "(2π)⁻¹" D (mkInvImageNear twoPi D)
  return (twoPi, invTwoPi)

/-- The named `T = t/2π` at the endpoint `tn/td`, from the sealed `(2π)⁻¹`. -/
meta def mkTNamedRS (tE htE : Expr) (tn td D : ℕ) : MetaM RNear := do
  let (_, invTwoPi) ← mkTwoPiSealed D
  let T ← mulNear (← mkConstNear tn td) invTwoPi
  let heT := mkAppN (mkConst ``t_div_two_pi_mk) #[tE, natLitShared tn, natLitShared td, htE]
  withPhase "RS: rename t/(2π)" (ofEqNearHe (← lemmaLhs heT) heT T)

/-- Main-sum steps between seals of the running sum. Each step nests the previous sum's proof one
level deeper, and the kernel checks that chain recursively against `maxRecDepth` (512 by default,
exceeded at height 10⁷: `ν ≈ 1262`, 631 steps). Sealing the sum as an auxiliary lemma every
`mainSumSealEvery` steps bounds the depth at any height. -/
meta def mainSumSealEvery : ℕ := 128

/-- Chooses extra precision for first-order term when needed: it involves four-fold division by
`cos 2πp` which, when `p` is close to 1/4 or 3/4, can lead to bit cancellation. -/
meta def c1ExtraBits (tn td ν : ℕ) : ℕ :=
  let pi := 3.141592653589793
  let p  := Float.sqrt (tn.toFloat / (td.toFloat * 2 * pi)) - ν.toFloat
  let c  := (Float.cos (2 * pi * p)).abs
  if c ≥ 1.0 then 0 else 4 * (Float.log2 (1.0 / c)).ceil.toUInt64.toNat

/-- The named enclosure of the Riemann–Siegel approximant at the endpoint `tn/td`: the full
`hardyZApproximantRS` when `withC₁`, else the linear-free `hardyZApproximantRS₀`, which skips the
whole `C₁` block. -/
meta def mkHardyZNamedRS (tE htE : Expr) (tn td D : ℕ) (withC₁ : Bool := true) :
    MetaM RNear := do
  let θ ← withPhase "RS: theta" (mkThetaNamedRS tE htE tn td D)
  let θE := θ.x
  let some ν := cutoffRS? tn td
  | throwError "mkHardyZNamedRS: endpoint {tn}/{td} lies within the d20 π-margin of a 2πk² \
    boundary; move the endpoint"
  let hν := mkAppN (mkConst ``floor_sqrt_eq_dec)
      #[tE, natLitShared tn, natLitShared td, natLitShared ν, htE, reflBoolTrue, reflBoolTrue,
        reflBoolTrue]
  let (twoPi, _) ← mkTwoPiSealed D
  let T ← mkTNamedRS tE htE tn td D
  let heT := mkAppN (mkConst ``t_div_two_pi_mk) #[tE, natLitShared tn, natLitShared td, htE]
  -- `√T` once: `C₀`, `T^{-1/4}` and the `C₁` assembly all start from it
  let sqrtT ← mkSqrtImageNear T D
  let S ← withPhase "RS: main sum" do
      -- every step input on the shared denominator `B`: θ per endpoint, the rest sealed per file
      let B := mainSumDenom D
      let θB ← recentreExactNear θ B
      let πM ← mkPiNearMain B
      let mut S : RNear ← recentreExactNear (← ofEqNearHe
        (mkApp3 (mkConst ``mainSumRS) θE tE (natLitShared 1))
        (mkApp2 (mkConst ``main_sum_rs_one) θE tE)
        (← mkCosImageNear θ D)) B
      let terms (n : ℕ) : MetaM (RNear × RNear) := do
        let logN ← withPhase "RS: log term" (sealedConst s!"log {n} main sum" B
          (do recentreExactNear (← cachedNear (mkLogNearOf n 1 D D)) B))
        let invSqrtN ← withPhase "RS: inv sqrt" (sealedConst s!"1/√{n} main sum" B
          (do recentreExactNear (← mkInvSqrtNatSealed n D) B))
        return (logN, invSqrtN)
      -- two terms per step (one rounding and one radius check per pair), a single step for an odd
      -- leftover; the running sum sealed every `mainSumSealEvery` steps
      let mut n := 2
      let mut steps := 0
      while n ≤ ν do
        if n + 1 ≤ ν then
          let (L₁, A₁) ← terms n
          let (L₂, A₂) ← terms (n + 1)
          S ← withPhase "RS: step pair" (mainSumPairNear S θB L₁ A₁ L₂ A₂ πM tE htE tn td n B)
          n := n + 2
        else
          let (L, A) ← terms n
          S ← withPhase "RS: step" (mainSumStepNear S θB L A πM tE htE tn td n B)
          n := n + 1
        steps := steps + 1
        if steps % mainSumSealEvery == 0 && n ≤ ν then
          S ← withPhase "RS: seal main sum" (cachedNear (pure S))
      S ← withPhase "RS: two mul" (addNear S S)
      let hSe := mkApp3 (mkConst ``main_sum_of_phase_eq) θE tE (natLitShared ν)
      ofEqNearHe (← lemmaLhs hSe) hSe S
  let Cmul : RNear ← withPhase "RS: fourth root term" do
    let root ← withPhase "RS: 4th root inv"
      (mkInvImageNear (← mkSqrtImageNear sqrtT D) D)
    let heQ := mkApp2 (mkConst ``rpow_neg_quarter_mk) T.x
      (mkAppN (mkConst ``t_div_two_pi_nonneg) #[tE, natLitShared tn, natLitShared td, htE])
    let root ← withPhase "RS: rename 1/⁴√(t/(2π))" (ofEqNearHe (← lemmaLhs heQ) heQ root)
    let sgn ← withPhase "RS : sign" do
      if ν % 2 == 0 then
        let he := mkApp2 (mkConst ``neg_one_pow_even_mk) (natLitShared ν) reflBoolTrue
        ofEqNearHe (← lemmaLhs he) he (← mkRatConstNear 1)
      else
        let he := mkApp2 (mkConst ``neg_one_pow_odd_mk) (natLitShared ν) reflBoolTrue
        ofEqNearHe (← lemmaLhs he) he (← mkRatConstNear (-1))
    (mulNear sgn root)
  let C₀ : RNear ← withPhase "RS : zero order term" do
    let p ← subNear sqrtT (← mkConstNear ν 1)
    let num_in ← mulNear twoPi
      (← subNear (← subNear (← mulNear p p) p) (← mkConstNear 1 16))
    let n ← mkCosImageNear num_in D
    let den_in ← mulNear twoPi p
    let d ← mkCosImageNear den_in D
    let raw ← mulNear (← mkInvSignedNear d D) n
    let he := mkApp2 (mkConst ``correction_mk) p.x
      (mkAppN (mkConst ``cos_two_pi_p_ne_zero_mk)
      #[tE, natLitShared tn, natLitShared td, natLitShared ν, htE, reflBoolTrue, reflBoolTrue, hν])
    ofEqNearHe (← lemmaLhs he) he raw
  unless withC₁ do
    return ← withPhase "RS: assemble" do
      let heZ := mkAppN (mkConst ``hardyZApproximantRS₀_eq) #[tE, natLitShared ν, hν]
      ofEqNearHe (← lemmaLhs heZ) heZ (← subNear S (← mulNear Cmul C₀))
  let C₁ : RNear ← withPhase "RS: first order term" do
    let bits := c1ExtraBits tn td ν
    if bits > 200 then
      throwError "mkHardyZNamedRS: first-order denominator term cos(2πp) at {tn}/{td} needs \
        {bits} extra bits; endpoint is too close to 1/4 or 3/4"
    let D₁ := D * 2 ^ bits
    let piN₁ ← sealedConst "π" D₁ (mkPiNear D₁)
    let (twoPi₁, invTwoPi₁) ← mkTwoPiSealed D₁
    let T₁ ← mulNear (← mkConstNear tn td) invTwoPi₁
    let T₁ ← ofEqNearHe (← lemmaLhs heT) heT T₁
    let p ← subNear (← mkSqrtImageNear T₁ D₁) (← mkConstNear ν 1)
    let φ ← mulNear twoPi₁ (← subNear (← subNear (← mulNear p p) p) (← mkConstNear 1 16))
    let φ' ← mulNear twoPi₁ (← subNear (← mulNear (← mkConstNear 2 1) p) (← mkConstNear 1 1))
    let φ'' ← sealedConst "4π" D₁ (mulNear (← mkConstNear 4 1) piN₁)
    let φ₂' ← mulNear φ' φ'
    let φ₃' ← mulNear φ₂' φ'
    -- each trig image / product below is built once and shared by every derivative that uses it
    let cosφ ← mkCosImageNear φ D₁
    let sinφ ← mkSinImageNear φ D₁
    let R₀ := cosφ
    let R₁ ← negNear (← mulNear φ' sinφ)
    let R₂ ← subNear (← negNear (← mulNear φ₂' cosφ)) (← mulNear φ'' sinφ)
    let R₃ ← subNear (← mulNear φ₃' sinφ)
      (← mulNear (← mulNear (← mulNear (← mkConstNear 3 1) φ') φ'') cosφ)
    let twoPiP ← mulNear twoPi₁ p
    let C ← mkCosImageNear twoPiP D₁
    let heC :=
        mkAppN (mkConst ``cos_two_pi_p_ne_zero_mk) #[tE, natLitShared tn, natLitShared td,
                                                            natLitShared ν, htE, reflBoolTrue,
                                                            reflBoolTrue, hν]
    let S ← mkSinImageNear twoPiP D₁
    let piSq₁ ← sealedConst "π²" D₁ (mulNear piN₁ piN₁)
    let fourPiSq₁ ← sealedConst "4π²" D₁ (mulNear (← mkConstNear 4 1) piSq₁)
    let eightPiCube₁ ← sealedConst "8π³" D₁
      (mulNear (← mkConstNear 8 1) (← mulNear piSq₁ piN₁))
    let C' ← negNear (← mulNear twoPi₁ S)
    let C'' ← negNear (← mulNear fourPiSq₁ C)
    let C''' ← mulNear eightPiCube₁ S
    let invC ← mkInvSignedNear C D₁
    let Ψ ← mulNear invC R₀
    let heΨ := mkAppN (mkConst ``correction_mk) #[p.x, heC]
    let Ψ ← ofEqNearHe (← lemmaLhs heΨ) heΨ Ψ
    let Ψ' ← mulNear invC (← subNear R₁ (← mulNear C' Ψ))
    let heΨ' := mkAppN (mkConst ``deriv_correction_mk) #[p.x, heC]
    let Ψ' ← ofEqNearHe (← lemmaLhs heΨ') heΨ' Ψ'
    let Ψ'' ← mulNear invC
      (← subNear (← subNear R₂ (← mulNear (← mulNear (← mkConstNear 2 1) C') Ψ'))
        (← mulNear C'' Ψ))
    let heΨ'' := mkAppN (mkConst ``iteratedDeriv_two_correction_mk) #[p.x, heC]
    let Ψ'' ← ofEqNearHe (← lemmaLhs heΨ'') heΨ'' Ψ''
    let Ψ''' ← mulNear invC
      (← subNear
        (← subNear (← subNear R₃ (← mulNear (← mulNear (← mkConstNear 3 1) C') Ψ''))
          (← mulNear (← mulNear (← mkConstNear 3 1) C'') Ψ'))
        (← mulNear C''' Ψ))
    let heΨ''' := mkAppN (mkConst ``iteratedDeriv_three_correction_mk) #[p.x, heC]
    let Ψ''' ← ofEqNearHe (← lemmaLhs heΨ''') heΨ''' Ψ'''
    let inv96PiSq₁ ← sealedConst "(96π²)⁻¹" D₁
      (mkInvImageNear (← mulNear (← mkConstNear 96 1) piSq₁) D₁)
    let C₁ ← negNear (← mulNear Ψ''' inv96PiSq₁)
    let heC₁ := mkApp (mkConst ``correctionLinear_mk) p.x
    ofEqNearHe (← lemmaLhs heC₁) heC₁ C₁
  withPhase "RS: assemble" do
    let heZ := mkAppN (mkConst ``hardyZApproximantRS_eq) #[tE, natLitShared ν, hν]
    ofEqNearHe (← lemmaLhs heZ) heZ
      (← subNear S (← mulNear Cmul (← addNear C₀ (← mulNear C₁ (← mkInvImageNear sqrtT D)))))

open Elab Term in
/-- `hardyZNamedRS% tn td D` : an enclosure of the NAMED Hardy `Z` approximant body. -/
elab "hardyZNamedRS% "  tnn:num tdn:num Dn:num : term => do
  let tn := tnn.getNat; let td := tdn.getNat
  let tE := sfracExpr false tn td
  let htE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) tE
  return (← mkHardyZNamedRS tE htE tn td Dn.getNat).proof

/-- Benchmark: the named Hardy `Z` value `Re(e^{iθ̃}·ζ̃)` at `t = 14.1`, `M = 3`, `N = 6` — the
full Tier-3 target (definitionally `hardyZApproximantEM 3 6 14.1`). Reference:
`≈ -0.0273608563`. -/
example := hardyZNamedRS% 1500 10 100000000

/-! ### The named error bound and the certificate tactics -/

/-- The named enclosure of `hardyZErrorBoundRS` (or, when `!withC₁`, of `hardyZErrorBoundRS₀`,
which adds the dropped linear term's `13/10·T^{-3/4}`) at the endpoint `tn/td`. -/
meta def mkErrStrongNamedRS (tE htE : Expr) (tn td D : ℕ) (withC₁ : Bool := true) :
    MetaM RNear := do
  let T ← mkTNamedRS tE htE tn td D
  let q ← withPhase "RS error : 4th root" (mkSqrtImageNear (← mkSqrtImageNear T D) D)
  let qT ← withPhase "RS error: 5/4th power" (mulNear q T)
  let T₅ ← withPhase "RS error: 5th power root inv" (mkInvImageNear qT D)
  let T₁₅ ← withPhase "RS error: 15th power root inv"
    (mkInvImageNear (← mulNear (← mulNear qT qT) qT) D)
  let err ← withPhase "RS error: main error"
    (addNear (← mulNear (← mkConstNear 25 4) T₅) (← mulNear (← mkConstNear 1 32) T₁₅))
  let err ← if withC₁ then pure err else
    withPhase "RS error: linear term" do
      addNear err (← mulNear (← mkConstNear 13 10)
        (← mkInvImageNear (← mulNear (← mulNear q q) q) D))
  let herr :=
      mkAppN (mkConst (if withC₁ then ``hardyZErrorBoundRS_mk else ``hardyZErrorBoundRS₀_mk))
    #[tE, natLitShared tn, natLitShared td, htE, reflBoolTrue, reflBoolTrue]
  ofEqNearHe (← lemmaLhs herr) herr err

/-- The canonical cached enclosure of `hardyZApproximantEM M N t`: built once per `(M, N, t, D)`,
stated at the canonical application so every obligation can rename it onto its goal by a refl
transport. Memoized per process (`hardyZNamedCache`). -/
meta def mkHardyZCachedRS (tE htE : Expr) (tn td D : ℕ) (withC₁ : Bool := true) :
    MetaM RNear := do
  let key := (tn, td, D)
  let cache := if withC₁ then hardyZNamedCacheRS else hardyZNamedCacheRS₀
  if let some (tE', r) := (← cache.get).get? key then
    if tE' == tE && (← proofsInEnv #[r.proof]) then
      return r
  let r ← cachedNear do
    let r ← mkHardyZNamedRS tE htE tn td D withC₁
    let xC := mkAppN (mkConst (if withC₁ then ``hardyZApproximantRS else ``hardyZApproximantRS₀))
      #[tE]
    ofEqNearAt xC (mkReflR r.x) r
  cache.modify (·.insert key (tE, r))
  return r

/-- A resolved Hardy-`Z` site: the subject expression `x` the proof is about, the literal cutoffs
`M`, `N`, and the endpoint `tE = sfrac false tn td` with its proof `htE` and numeric height `tn/td`.
The goal-facing tactics obtain this by parsing the goal; `build_certs` fills it straight from the
row, so the endpoint value is used as it stands rather than rebuilt into a term and reparsed. -/
structure HardyZSiteRS where
  /-- The subject expression the enclosure is transported onto. -/
  x : Expr
  /-- Bernoulli-term count. -/
  tn : ℕ
  /-- Height denominator. -/
  td : ℕ
  /-- Proof `tE = sfrac false tn td`. -/
  htE : Expr
  /-- The endpoint expression `sfrac false tn td`. -/
  tE : Expr
  /-- Proof `x = hardyZApproximantRS tE`, transporting the cached enclosure onto the subject
  through a cited equality rather than a `mkReflR` defeq: in the `build_certs` path `x` is a
  `ZIntervalRS.fstVal`/`sndVal` wrapper, so this is `fstVal_mkZIRS`/`sndVal_mkZIRS`; in the
  goal-facing path `x` is already `hardyZApproximantRS tE`, so it is a reflexivity. -/
  he : Expr

/-- The height-scaled default working precision for a site: enclosure noise grows ~linearly in `t`
(the `t/2·log π` phase product), so `D` scales with the height to keep the margin uniform. -/
meta def siteDRS (s : HardyZSiteRS) (D? : Option ℕ) : ℕ :=
  D?.getD (100000000 * max 1 (s.tn / (30 * s.td)))

open Elab Tactic Term in
/-- Parse a subject expression `x` (reducing to `hardyZApproximantEM M N t`) into its resolved
`HardyZSite`; rejects a nonpositive `t`. The goal-facing tactics use this to recover the site the
`build_certs` path already holds. -/
meta def resolveHardyZSiteRS (x : Expr) (who : String) : MetaM HardyZSiteRS := do
  let x' ← headTo x ``hardyZApproximantRS
  let args := x'.getAppArgs
  unless x'.getAppFn.constName? == some ``hardyZApproximantRS && args.size == 1 do
    throwError "{who}: expected `hardyZApproximantRS t`, got {x}"
  let (tneg, tn, td, htE, tE) ← recognizeRat' args[0]!
  if tneg || tn == 0 then throwError "{who}: t must be positive"
  -- the goal-facing subject already reduces to `hardyZApproximantRS tE`, so the transport is a
  -- reflexivity (the cached enclosure is stated at exactly this application)
  return { x, tn, td, htE, tE, he := mkReflR (mkAppN (mkConst ``hardyZApproximantRS) #[tE]) }

/-- The named enclosure of one site's Hardy-`Z` value, transported onto the site's subject `x`. -/
meta def mkHardyZSiteNearRS (s : HardyZSiteRS) (D? : Option ℕ := none) (withC₁ : Bool := true) :
    MetaM RNear := do
  let r ← withPhase s!"hardyZ enclosure t={s.tn}/{s.td}"
    (mkHardyZCachedRS s.tE s.htE s.tn s.td (siteDRS s D?) withC₁)
  ofEqNearAt s.x s.he r

/-- Core of `hardy_sign_change` on two resolved sites: enclose both, extract their signs
(`neg_val`/`pos_val`), and combine into `sa.x * sb.x < 0`. -/
meta def hardySignChangeSitesRS (sa sb : HardyZSiteRS) (D? : Option ℕ := none)
    (withC₁ : Bool := true) : MetaM Expr := do
  let mkSide (s : HardyZSiteRS) : MetaM (RNear × Expr) := do
    let named ← mkHardyZSiteNearRS s D? withC₁
    unless named.rn * named.cd < named.cn * named.rd do
      throwError "hardy_sign_change_rs: the enclosure of Z̃ at {s.tE} does not separate from \
        zero at working precision {siteDRS s D?}"
    return (named, s.x)
  let (ra, aE) ← mkSide sa
  let (rb, bE) ← mkSide sb
  let mkSignPf (x : Expr) (r : RNear) : Expr :=
    mkAppN (mkConst (if r.neg then ``Real.IsNear.neg_val else ``Real.IsNear.pos_val))
      #[x, natLitShared r.cn, natLitShared r.cd, natLitShared r.rn, natLitShared r.rd, r.proof,
        reflBoolTrue, reflBoolTrue, reflBoolTrue]
  if ra.neg && !rb.neg then
    return mkAppN (mkConst ``mul_neg_of_neg_pos_r) #[aE, bE, mkSignPf aE ra, mkSignPf bE rb]
  else if !ra.neg && rb.neg then
    return mkAppN (mkConst ``mul_neg_of_pos_neg_r) #[aE, bE, mkSignPf aE ra, mkSignPf bE rb]
  else throwError "hardy_sign_change_rs: both endpoint values have the same sign"

/-- Goal-facing `hardy_sign_change` core: parse both product factors into sites, then delegate to
`hardySignChangeSitesRS`. -/
meta def hardySignChangeCoreRS (a b : Expr) (D? : Option ℕ := none) : MetaM Expr := do
  hardySignChangeSitesRS (← resolveHardyZSiteRS a "hardy_sign_change")
    (← resolveHardyZSiteRS b "hardy_sign_change") D?

open Elab Tactic Term in
/-- `hardy_sign_change_rs` closes `hardyZApproximantRS tl * hardyZApproximantRS tr < 0`:
builds named enclosures of both factors, extracts the two signs (`neg_val`/`pos_val`), and
combines them. `t` arguments in any recognised rational surface form; each factor may sit
behind a reducible wrapper (e.g. `ZeroInterval.leftVal I` for a literal `I`). -/
elab "hardy_sign_change_rs" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr LT.lt _ _ lhs _ := ty
    | throwError "hardy_sign_change_rs: goal must be `Z̃(l) * Z̃(r) < 0`"
  let_expr HMul.hMul _ _ _ _ a b := lhs
    | throwError "hardy_sign_change_rs: expected a product on the left"
  let pf ← hardySignChangeCoreRS a b
  liftMetaFinishingTactic (·.assign pf)

/-- Whether `‖x‖ > e` follows from the enclosures `hx`, `he` by `norm_gt_of_isNear`: the meta
mirror of its `Nat.blt` condition. -/
meta def normGtMarginOk (hx he : RNear) : Bool :=
  let eUp := (if he.neg then 0 else he.cn) * (he.rd * (hx.cd * hx.rd))
    + he.rn * (he.cd * (hx.cd * hx.rd)) + hx.rn * (he.cd * (he.rd * hx.cd))
  let xLo := hx.cn * (he.cd * (he.rd * hx.rd))
    + (if he.neg then he.cn else 0) * (he.rd * (hx.cd * hx.rd))
  eUp < xLo

/-- `norm_gt_of_isNear` at `x`, `e` with the enclosures `hx`, `he`. -/
meta def mkNormGtOfIsNear (x e : Expr) (hx he : RNear) : Expr :=
  mkAppN (mkConst ``norm_gt_of_isNear)
    #[x, e, toExpr hx.neg, toExpr he.neg, natLitShared hx.cn, natLitShared hx.cd,
      natLitShared hx.rn, natLitShared hx.rd, natLitShared he.cn, natLitShared he.cd,
      natLitShared he.rn, natLitShared he.rd, hx.proof, he.proof, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue]

/-- The error bound (`hardyZErrorBoundRS`, or `…RS₀` when `!withC₁`) at a batch's lowest endpoint
`sn/sd`, enclosed and sealed once per batch (memo `errBoundLoCacheRS`). Returns the endpoint
expression `sfrac false sn sd` and the enclosure, named at the bound applied to it. -/
meta def mkErrBoundLoRS (sn sd D : ℕ) (withC₁ : Bool) : MetaM (Expr × RNear) := do
  let sE := mkSfracR false sn sd
  let key := (sn, sd, D, withC₁)
  if let some r := (← errBoundLoCacheRS.get)[key]? then
    if ← proofsInEnv #[r.proof] then return (sE, r)
  let hsE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) sE
  let r ← cachedNear (mkErrStrongNamedRS sE hsE sn sd D withC₁)
  errBoundLoCacheRS.modify (·.insert key r)
  return (sE, r)

/-- Core of `hardy_error_ok` on a resolved site `s` and a bound `bnd` (the error bound at `s.tE`):
build the named enclosures, meta-check the margin, and return a proof of `‖s.x‖ > bnd`.

With `lo? = some (sn, sd)`, the batch's lowest endpoint (`sn/sd ≤ s.tn/s.td`), the error bound is
first tried at `sn/sd` — one sealed enclosure per batch — and moved up to `s.tE` by antitonicity
(`norm_gt_hardyZErrorBoundRS(₀)_of_le`). The bound decreases in `t`, so this only costs margin;
where that margin is not enough (wide low-`t` batches) the endpoint's own bound is used instead. -/
meta def hardyErrOkSiteRS (s : HardyZSiteRS) (bnd : Expr) (D? : Option ℕ := none)
    (withC₁ : Bool := true) (lo? : Option (ℕ × ℕ) := none) : MetaM Expr := do
  let D := siteDRS s D?
  let rZ ← withPhase s!"hardyZ enclosure t={s.tn}/{s.td}"
    (mkHardyZCachedRS s.tE s.htE s.tn s.td D withC₁)
  let hx ← ofEqNearAt s.x s.he rZ
  if let some (sn, sd) := lo? then
    if 1 ≤ sn && 1 ≤ sd && 1 ≤ s.td && sn * s.td ≤ s.tn * sd then
      let (sE, rLo) ← withPhase "errStrong enclosure (batch)" (mkErrBoundLoRS sn sd D withC₁)
      let bndLo := mkApp (mkConst (if withC₁ then ``hardyZErrorBoundRS else ``hardyZErrorBoundRS₀))
        sE
      let heLo ← ofEqNearAt bndLo (mkReflR rLo.x) rLo
      if normGtMarginOk hx heLo then
        let hsE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) sE
        return mkAppN (mkConst (if withC₁ then ``norm_gt_hardyZErrorBoundRS_of_le
            else ``norm_gt_hardyZErrorBoundRS₀_of_le))
          #[s.x, sE, s.tE, natLitShared sn, natLitShared sd, natLitShared s.tn, natLitShared s.td,
            hsE, s.htE, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
            mkNormGtOfIsNear s.x bndLo hx heLo]
  let rE ← withPhase s!"errStrong enclosure t={s.tn}/{s.td}"
    (cachedNear (mkErrStrongNamedRS s.tE s.htE s.tn s.td D withC₁))
  let he ← ofEqNearAt bnd (mkReflR rE.x) rE
  -- meta-check the margin before emitting the kernel condition
  unless normGtMarginOk hx he do
    throwError "hardy_error_ok_rs: at {s.tE}, the error bound is not below |Z̃| at working \
      precision {D}"
  return mkNormGtOfIsNear s.x bnd hx he

/-- Goal-facing `hardy_error_ok` core: parse the subject `x` into a site, then delegate to
`hardyErrOkSite`. -/
meta def hardyErrOkCoreRS (x bnd : Expr) (D? : Option ℕ := none) : MetaM Expr := do
  hardyErrOkSiteRS (← resolveHardyZSiteRS x "hardy_error_ok") bnd D?

open Elab Tactic Term in
/-- `hardy_error_ok` closes `‖hardyZApproximantRS t‖ > hardyZErrorBoundStrongRS t`: named
enclosures of the value and the strengthened error bound, compared by `norm_gt_of_isNear`. -/
elab "hardy_error_ok_rs" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr GT.gt _ _ lhs rhs := ty
    | throwError "hardy_error_ok_rs: goal must be `‖Z̃(t)‖ > hardyZErrorBoundRS t`"
  let_expr Norm.norm _ _ x := lhs
    | throwError "hardy_error_ok_rs: expected a norm on the left"
  let pf ← hardyErrOkCoreRS x rhs
  liftMetaFinishingTactic (·.assign pf)

/-! ### The first-zero certificate

The three Certificate obligations for the interval `[149.5, 150.49]`,
each discharged by one tactic call. -/

/-- The endpoint values change sign across `[149.5, 150.49]`. -/
theorem first_zero_sign_change_rs :
    hardyZApproximantRS 149.5 * hardyZApproximantRS 150.49 < 0 := by
  hardy_sign_change_rs

/-- The left endpoint value clears the strengthened error bound. -/
theorem first_zero_left_error_rs :
    ‖hardyZApproximantRS 149.5‖ > hardyZErrorBoundRS 149.5 := by
  hardy_error_ok_rs

/-- The right endpoint value clears the strengthened error bound. -/
theorem first_zero_right_error_rs :
    ‖hardyZApproximantRS 150.49‖ > hardyZErrorBoundRS 150.49 := by
  hardy_error_ok_rs

end BSN
