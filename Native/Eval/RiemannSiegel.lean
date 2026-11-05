module

public import Enclosure.Defs
public import Enclosure.BinarySplit.Defs
public import Native.Eval.Log
public import Native.Eval.Arctan
public import Native.Eval.Fix

/-!
# `Native.Eval.RiemannSiegel`: the computable part

The definitions `native_decide` evaluates, free of `Mathlib` so that they compile natively (the
`NativeEval` library is built with `precompileModules`). Their soundness theorems are in
`Native.RiemannSiegel`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

/-- The side conditions of `BSN.floor_sqrt_eq_dec`. -/
def cutoffOk (tn td ν : Nat) : Bool :=
  Nat.ble 1 td &&
  Nat.ble (Nat.mul (Nat.mul 628318530717958647694 (Nat.mul ν ν)) td)
    (Nat.mul 100000000000000000000 tn) &&
  Nat.blt (Nat.mul 100000000000000000000 tn)
    (Nat.mul (Nat.mul 628318530717958647692 (Nat.mul (ν + 1) (ν + 1))) td)

/-- `⌊√(t/2π)⌋` at `t = tn/td`, or `none` when `t` is too close to a boundary `2πk²` for the
20-digit bounds on `π` to decide it. -/
def cutoff (tn td : Nat) : Option Nat :=
  let ν := Nat.sqrt (100000000000000000000 * tn / (628318530717958647693 * td))
  if cutoffOk tn td ν then some ν else none

/-- `2π`, as `sfrac false 2 1 * π`. -/
def twoPi : Option Encl := (Encl.const false 2 1).mul piEncl

/-- `T = t/2π` at `t = tn/td`, on the grid `1/Q`. -/
def tDivTwoPi (tn td Q : Nat) : Option Encl :=
  twoPi.bind fun P => (P.inv Q).bind fun P' => Encl.mulR (Encl.const false tn td) P' Q

/-- The literal constants of `BSN.riemannSiegelThetaApproximant_two_zero_mk` at `t = tn/td`. -/
structure ThetaConsts where
  S : Nat
  Q : Nat
  V : Nat
  T4 : Nat
  T2 : Nat
  Rn : Nat
  Rd : Nat

/-- The constants: `S/Q = 1/16 + t²/4`, `V = 2tn`, `T4 = 4td`, `T2 = 2td`, and the rational tail
`Rn/Rd`. -/
def thetaConsts (tn td : Nat) : ThetaConsts :=
  let S := td * td + 4 * tn * tn
  ⟨S, 16 * td * td, 2 * tn, 4 * td, 2 * td,
    30 * tn * td * S ^ 2 + 64 * tn ^ 3 * td ^ 3 - 48 * tn * td ^ 5, 45 * S ^ 3⟩

/-- The side conditions of `BSN.riemannSiegelThetaApproximant_two_zero_mk`. -/
def thetaOk (tn td : Nat) (c : ThetaConsts) : Bool :=
  Nat.ble 1 tn && Nat.ble 1 td &&
  Nat.beq c.S ((td.mul td).add ((Nat.mul 4 tn).mul tn)) &&
  Nat.beq c.Q ((Nat.mul 16 td).mul td) && Nat.beq c.V (Nat.mul 2 tn) &&
  Nat.beq c.T4 (Nat.mul 4 td) && Nat.beq c.T2 (Nat.mul 2 td) &&
  Nat.beq (c.Rn.add ((Nat.mul 48 tn).mul (td.pow 5)))
    (((Nat.mul 30 tn).mul td).mul (c.S.pow 2) |>.add ((Nat.mul 64 (tn.pow 3)).mul (td.pow 3))) &&
  Nat.beq c.Rd (Nat.mul 45 (c.S.pow 3))

/-- `θ̃(t)` at `t = tn/td`, along `BSN.riemannSiegelThetaApproximant_two_zero_mk`, for given
constants `c` (checked by `thetaOk`) and grid `1/Q`:
`(tn/4td)·log(S/Q) − ¼(½π − arctan(td/V)) − tn/2td − (tn/2td)·log π − Rn/Rd`. -/
def thetaWith (tn td W Q : Nat) (c : ThetaConsts) (logPi : Option Encl) : Option Encl :=
  if thetaOk tn td c then
    (logRatSigned c.S c.Q W).bind fun lSQ =>
    (Encl.mulR (Encl.const false tn c.T4) lSQ Q).bind fun a₁ =>
    (arctanRat td c.V W).bind fun atn =>
    (Encl.mulR (Encl.const false 1 2) piEncl Q).bind fun hp =>
    (Encl.subR hp atn Q).bind fun d =>
    (Encl.mulR (Encl.const false 1 4) d Q).bind fun a₂ =>
    logPi.bind fun lp =>
    (Encl.mulR (Encl.const false tn c.T2) lp Q).bind fun a₃ =>
    (Encl.subR a₁ a₂ Q).bind fun s₁ =>
    (Encl.subR s₁ (Encl.const false tn c.T2) Q).bind fun s₂ =>
    (Encl.subR s₂ a₃ Q).bind fun s₃ =>
    Encl.addR s₃ (Encl.const true c.Rn c.Rd) Q
  else none

/-- `θ̃(t)` at `t = tn/td`, to about `1/W`. -/
def theta (tn td W : Nat) (logPi : Option Encl) : Option Encl :=
  thetaWith tn td W (dyadic W) (thetaConsts tn td) logPi

/-- The side conditions of `thetaF`: those of `thetaWith`, and positive denominators for the
rational constants. -/
def thetaFOk (tn td : Nat) (c : ThetaConsts) : Bool :=
  thetaOk tn td c && Nat.ble 1 c.T4 && Nat.ble 1 c.T2 && Nat.ble 1 c.Rd

/-- `θ̃(t)` at `t = tn/td` on the grid `1/Q`, along `BSN.riemannSiegelThetaApproximant_two_zero_mk`
like `thetaWith`, with the arithmetic in `Fx`; `H` encloses `π/2` and `lp` encloses `log π`. -/
def thetaF (tn td W Q : Nat) (c : ThetaConsts) (H lp : Fx) : Option Fx :=
  if thetaFOk tn td c then
    (logRatSigned c.S c.Q W).bind fun lSQ => (Fx.ofEncl Q lSQ).bind fun L =>
    (arctanRat td c.V W).bind fun atn => (Fx.ofEncl Q atn).map fun A =>
    Fx.add (Fx.sub (Fx.sub (Fx.sub (Fx.mul Q (Fx.ofRat false tn c.T4 Q) L)
        (Fx.divNat 4 (Fx.sub H A))) (Fx.ofRat false tn c.T2 Q))
        (Fx.mul Q (Fx.ofRat false tn c.T2 Q) lp))
      (Fx.ofRat true c.Rn c.Rd Q)
  else none

/-- `(√n)⁻¹`. -/
def invSqrtNat (n Q : Nat) : Option Encl := ((Encl.const false n 1).sqrt Q).bind (·.inv Q)

/-- Per-batch data for the main sum, on the fixed-point grid `1/Q`: `π/2`, and `log n` and
`(√n)⁻¹` for `n ≤ N`, computed once for the whole batch rather than at every endpoint. -/
structure TermTable where
  Q : Nat
  H : Option Fx
  trig : Array (Option (Fx × Fx))
  tp : Option Fx
  itp : Option Fx
  logPi : Option Encl
  logPiF : Option Fx
  lg : Array (Option Fx)
  isq : Array (Option Fx)

/-- The table for `n ≤ N`, with leaves to `1/W` on the grid `1/dyadic W`. -/
def termTable (N W : Nat) : TermTable :=
  { Q := dyadic W
    H := (Fx.ofEncl (dyadic W) piEncl).map (Fx.divNat 2)
    trig := match (Fx.ofEncl (dyadic W) piEncl).map (Fx.divNat 2) with
      | some H => Fx.trigTable (dyadic W) H
      | none => #[]
    tp := twoPi.bind (Fx.ofEncl (dyadic W))
    itp := (twoPi.bind (·.inv (dyadic W))).bind (Fx.ofEncl (dyadic W))
    logPi := log piEncl W
    logPiF := (log piEncl W).bind (Fx.ofEncl (dyadic W))
    lg := Array.ofFn (n := N + 1) fun i => (logNat i W).bind (Fx.ofEncl (dyadic W))
    isq := Array.ofFn (n := N + 1) fun i => (invSqrtNat i (dyadic W)).bind (Fx.ofEncl (dyadic W)) }

/-- `(cos x, sin x)` as `Encl`s, through the table's fixed-point grid. -/
def cosSinE (tab : TermTable) (X : Encl) : Option (Encl × Encl) :=
  tab.H.bind fun H => (Fx.ofEncl tab.Q X).bind fun XF =>
    (Fx.cosSinT tab.Q H tab.trig XF).map fun cs => (Fx.toEncl tab.Q cs.1, Fx.toEncl tab.Q cs.2)

/-- `log n` from the table, or computed if the table stops short. -/
def lgAt (tab : TermTable) (n W : Nat) : Option Fx :=
  match tab.lg[n]? with
  | some o => o
  | none => (logNat n W).bind (Fx.ofEncl tab.Q)

/-- `(√n)⁻¹` from the table, or computed if the table stops short. -/
def isqAt (tab : TermTable) (n : Nat) : Option Fx :=
  match tab.isq[n]? with
  | some o => o
  | none => (invSqrtNat n tab.Q).bind (Fx.ofEncl tab.Q)

/-- The smallest factor `d ≥ 2` of `n` by trial division (`n` itself if none is found below
`√n`), with `fuel` steps. Any value is sound: the angle table checks `d · (n/d) = n`. -/
def smallFactor (n : Nat) : Nat → Nat → Nat
  | 0, _ => n
  | fuel + 1, d => if n < d * d then n else if n % d == 0 then d else smallFactor n fuel (d + 1)

/-- The next entry of the phase table: `(cos(t log n), sin(t log n))` at `n = arr.size`, given the
entries below it. `n ≤ 1` has phase `0`; a composite `n = p·m` rotates the entries `p` and `m`;
a prime is evaluated directly. `H` encloses `π/2`, `T` encloses `t`. -/
def angleEntry (tab : TermTable) (H T : Fx) (W : Nat) (arr : Array (Option (Fx × Fx))) :
    Option (Fx × Fx) :=
  if arr.size ≤ 1 then some (Fx.ofInt tab.Q 1, Fx.zero)
  else if smallFactor arr.size arr.size 2 < arr.size &&
      smallFactor arr.size arr.size 2 * (arr.size / smallFactor arr.size arr.size 2) == arr.size
  then
    (arr[smallFactor arr.size arr.size 2]?.join).bind fun a =>
      (arr[arr.size / smallFactor arr.size arr.size 2]?.join).map fun b => Fx.rotate tab.Q a b
  else (lgAt tab arr.size W).bind fun L => Fx.cosSinT tab.Q H tab.trig (Fx.mul tab.Q T L)

/-- Extend the phase table by `k` entries. -/
def anglesAux (tab : TermTable) (H T : Fx) (W : Nat) :
    Nat → Array (Option (Fx × Fx)) → Array (Option (Fx × Fx))
  | 0, arr => arr
  | k + 1, arr => anglesAux tab H T W k (arr.push (angleEntry tab H T W arr))

/-- The two sums `∑ cos(t log n)·(√n)⁻¹` and `∑ sin(t log n)·(√n)⁻¹` over `n = 1, …, ν`, from the
phase table `A`. -/
def sumTerms (tab : TermTable) (A : Array (Option (Fx × Fx))) : Nat → Option (Fx × Fx)
  | 0 => some (Fx.zero, Fx.zero)
  | k + 1 => (sumTerms tab A k).bind fun S =>
      (A[k + 1]?.join).bind fun cs => (isqAt tab (k + 1)).map fun isq =>
        (Fx.add S.1 (Fx.mul tab.Q cs.1 isq), Fx.add S.2 (Fx.mul tab.Q cs.2 isq))

/-- The main sum `∑_{n ≤ ν} cos(θ − t log n)/√n = cos θ·∑ cos(t log n)/√n + sin θ·∑ sin(t log n)/√n`
at `t = tn/td`, for an enclosure `θ` of the phase, on the table's fixed-point grid. -/
def mainSumF (θ : Fx) (tn td : Nat) (tab : TermTable) (W ν : Nat) : Option Fx :=
  if Nat.ble 1 td then
    tab.H.bind fun H => (Fx.cosSinT tab.Q H tab.trig θ).bind fun cs =>
      (sumTerms tab (anglesAux tab H (Fx.ofRat false tn td tab.Q) W (ν + 1) #[]) ν).map fun S =>
        Fx.add (Fx.mul tab.Q cs.1 (Fx.tighten tab.Q S.1)) (Fx.mul tab.Q cs.2 (Fx.tighten tab.Q S.2))
  else none

/-- `mainSumF` from an `Encl` phase, returned as an `Encl`. -/
def mainSum (θE : Encl) (tn td : Nat) (tab : TermTable) (W ν : Nat) : Option Encl :=
  (Fx.ofEncl tab.Q θE).bind fun θ => (mainSumF θ tn td tab W ν).map (Fx.toEncl tab.Q)

/-- The leaves shared by `Ψ` and its derivatives, at an enclosure `P` of `p`: `2π`, `C = cos 2πp`,
`S = sin 2πp`, `C⁻¹`, and `cos φ`, `sin φ` for `φ = 2π(p² − p − 1/16)`. -/
structure CorrLeaves where
  tp : Encl
  C : Encl
  S : Encl
  iC : Encl
  cφ : Encl
  sφ : Encl

/-- Compute `CorrLeaves` at `P`. -/
def corrLeaves (tab : TermTable) (P : Encl) (Q : Nat) : Option CorrLeaves :=
  twoPi.bind fun tp =>
  (Encl.mulR tp P Q).bind fun a =>
  (cosSinE tab a).bind fun CS =>
  (CS.1.inv Q).bind fun iC =>
  (Encl.mulR P P Q).bind fun pp =>
  (Encl.subR pp P Q).bind fun q₁ =>
  (Encl.subR q₁ (Encl.const false 1 16) Q).bind fun q₂ =>
  (Encl.mulR tp q₂ Q).bind fun b =>
  (cosSinE tab b).bind fun cs =>
  some ⟨tp, CS.1, CS.2, iC, cs.1, cs.2⟩

/-- `Ψ(p) = C⁻¹·cos φ` (`BSN.correction_mk`). -/
def correction (L : CorrLeaves) (Q : Nat) : Option Encl := Encl.mulR L.iC L.cφ Q

/-- `A = 2π(2p − 1)`, the derivative of `φ`. -/
def corrA (L : CorrLeaves) (P : Encl) (Q : Nat) : Option Encl :=
  (Encl.mulR (Encl.const false 2 1) P Q).bind fun p₂ =>
  (Encl.subR p₂ (Encl.const false 1 1) Q).bind fun d => Encl.mulR L.tp d Q

/-- The non-leaf pieces of the derivative chain: `A = 2π(2p − 1)`, `Y = 2π·sin 2πp`, `π²`, `π³`,
and `Z₂ = 4π²·cos 2πp`. -/
structure CorrAux where
  A : Encl
  Y : Encl
  pi2 : Encl
  pi3 : Encl
  Z₂ : Encl

/-- Compute `CorrAux`. -/
def corrAux (L : CorrLeaves) (P : Encl) (Q : Nat) : Option CorrAux :=
  (corrA L P Q).bind fun A =>
  (Encl.mulR L.tp L.S Q).bind fun Y =>
  (Encl.mulR piEncl piEncl Q).bind fun pi2 =>
  (Encl.mulR pi2 piEncl Q).bind fun pi3 =>
  (Encl.mulR (Encl.const false 4 1) pi2 Q).bind fun f =>
  (Encl.mulR f L.C Q).bind fun Z₂ =>
  some ⟨A, Y, pi2, pi3, Z₂⟩

/-- `Ψ' = C⁻¹·(−(A·sin φ) − (−Y)·Ψ)` (`BSN.deriv_correction_mk`). -/
def deriv1 (L : CorrLeaves) (X : CorrAux) (ψ : Encl) (Q : Nat) : Option Encl :=
  (Encl.mulR X.A L.sφ Q).bind fun a =>
  (Encl.mulR X.Y.negate ψ Q).bind fun b =>
  (Encl.subR a.negate b Q).bind fun c => Encl.mulR L.iC c Q

/-- `Ψ'' = C⁻¹·(−(A·A·cos φ) − 4π·sin φ − 2·(−Y)·Ψ' − (−Z₂)·Ψ)`
(`BSN.iteratedDeriv_two_correction_mk`). -/
def deriv2 (L : CorrLeaves) (X : CorrAux) (ψ ψ₁ : Encl) (Q : Nat) : Option Encl :=
  (Encl.mulR X.A X.A Q).bind fun aa =>
  (Encl.mulR aa L.cφ Q).bind fun t₁ =>
  (Encl.mulR (Encl.const false 4 1) piEncl Q).bind fun fp =>
  (Encl.mulR fp L.sφ Q).bind fun t₂ =>
  (Encl.mulR (Encl.const false 2 1) X.Y.negate Q).bind fun ty =>
  (Encl.mulR ty ψ₁ Q).bind fun t₃ =>
  (Encl.mulR X.Z₂.negate ψ Q).bind fun t₄ =>
  (Encl.subR t₁.negate t₂ Q).bind fun s₁ =>
  (Encl.subR s₁ t₃ Q).bind fun s₂ =>
  (Encl.subR s₂ t₄ Q).bind fun s₃ => Encl.mulR L.iC s₃ Q

/-- `Ψ‴ = C⁻¹·(A·A·A·sin φ − 3·A·4π·cos φ − 3·(−Y)·Ψ″ − 3·(−Z₂)·Ψ′ − 8π³·S·Ψ)`
(`BSN.iteratedDeriv_three_correction_mk`). -/
def deriv3 (L : CorrLeaves) (X : CorrAux) (ψ ψ₁ ψ₂ : Encl) (Q : Nat) : Option Encl :=
  (Encl.mulR X.A X.A Q).bind fun aa =>
  (Encl.mulR aa X.A Q).bind fun aaa =>
  (Encl.mulR aaa L.sφ Q).bind fun t₁ =>
  (Encl.mulR (Encl.const false 3 1) X.A Q).bind fun ta =>
  (Encl.mulR (Encl.const false 4 1) piEncl Q).bind fun fp =>
  (Encl.mulR ta fp Q).bind fun tafp =>
  (Encl.mulR tafp L.cφ Q).bind fun t₂ =>
  (Encl.mulR (Encl.const false 3 1) X.Y.negate Q).bind fun ty =>
  (Encl.mulR ty ψ₂ Q).bind fun t₃ =>
  (Encl.mulR (Encl.const false 3 1) X.Z₂.negate Q).bind fun tz =>
  (Encl.mulR tz ψ₁ Q).bind fun t₄ =>
  (Encl.mulR (Encl.const false 8 1) X.pi3 Q).bind fun ep =>
  (Encl.mulR ep L.S Q).bind fun eps =>
  (Encl.mulR eps ψ Q).bind fun t₅ =>
  (Encl.subR t₁ t₂ Q).bind fun s₁ =>
  (Encl.subR s₁ t₃ Q).bind fun s₂ =>
  (Encl.subR s₂ t₄ Q).bind fun s₃ =>
  (Encl.subR s₃ t₅ Q).bind fun s₄ => Encl.mulR L.iC s₄ Q

/-- `C₁ = −(Ψ‴·(96π²)⁻¹)` (`BSN.correctionLinear_mk`). -/
def correctionLinear (X : CorrAux) (ψ₃ : Encl) (Q : Nat) : Option Encl :=
  (Encl.mulR (Encl.const false 96 1) X.pi2 Q).bind fun n =>
  (n.inv Q).bind fun i => (Encl.mulR ψ₃ i Q).map Encl.negate

/-- `C₁(p)` from the leaves and `Ψ(p)`, through `Ψ′`, `Ψ″`, `Ψ‴`. -/
def corrLinear (L : CorrLeaves) (P ψ : Encl) (Q : Nat) : Option Encl :=
  (corrAux L P Q).bind fun X =>
  (deriv1 L X ψ Q).bind fun ψ₁ =>
  (deriv2 L X ψ ψ₁ Q).bind fun ψ₂ =>
  (deriv3 L X ψ ψ₁ ψ₂ Q).bind fun ψ₃ =>
  correctionLinear X ψ₃ Q

/-- The pieces both approximants share at `t = tn/td` with cutoff `ν`: `2·∑` (the main sum at
`θ̃`), `√T`, `(−1)^ν·T^{−1/4}`, an enclosure `P` of `p = √T − ν`, and the correction leaves at
`P`. -/
structure ApproxParts where
  S₂ : Encl
  sqT : Encl
  sgnq : Encl
  P : Encl
  L : CorrLeaves

/-- Compute `ApproxParts`. -/
def approxParts (tab : TermTable) (tn td W Q ν : Nat) : Option ApproxParts :=
  (theta tn td W tab.logPi).bind fun θE =>
  (mainSum θE tn td tab W ν).bind fun S =>
  (Encl.mulR (Encl.const false 2 1) S Q).bind fun S₂ =>
  (tDivTwoPi tn td Q).bind fun T =>
  (T.sqrt Q).bind fun sqT =>
  (sqT.sqrt Q).bind fun q =>
  (q.inv Q).bind fun iq =>
  (Encl.mulR (Encl.const (ν % 2 == 1) 1 1) iq Q).bind fun sgnq =>
  (Encl.subR sqT (Encl.const false ν 1) Q).bind fun P =>
  (corrLeaves tab P Q).bind fun L =>
  some ⟨S₂, sqT, sgnq, P, L⟩

/-- `hardyZApproximantRS₀ t` from its parts (`BSN.hardyZApproximantRS₀_eq`):
`2·∑ − (−1)^ν·T^{−1/4}·Ψ(p)`. -/
def approx₀Of (A : ApproxParts) (Q : Nat) : Option Encl :=
  (correction A.L Q).bind fun ψ =>
  (Encl.mulR A.sgnq ψ Q).bind fun b => Encl.subR A.S₂ b Q

/-- `hardyZApproximantRS t` from its parts (`BSN.hardyZApproximantRS_eq`):
`2·∑ − (−1)^ν·T^{−1/4}·(Ψ(p) + C₁(p)·(√T)⁻¹)`. -/
def approx₁Of (A : ApproxParts) (Q : Nat) : Option Encl :=
  (correction A.L Q).bind fun ψ =>
  (corrLinear A.L A.P ψ Q).bind fun c₁ =>
  (A.sqT.inv Q).bind fun isq =>
  (Encl.mulR c₁ isq Q).bind fun c =>
  (Encl.addR ψ c Q).bind fun k =>
  (Encl.mulR A.sgnq k Q).bind fun b => Encl.subR A.S₂ b Q

/-- `cos 2πp ≠ 0` at the cutoff's `p`, from the endpoint's positivity checks. -/
def endpointPos (tn td : Nat) : Bool := Nat.ble 1 tn && Nat.ble 1 td

/-- The approximants' shared parts at `t = tn/td` with its cutoff, if `t` is positive and the
cutoff decided. -/
def approxPartsAt (tab : TermTable) (tn td W : Nat) : Option (Nat × ApproxParts) :=
  if endpointPos tn td then
    (cutoff tn td).bind fun ν => (approxParts tab tn td W (dyadic W) ν).map fun A => (ν, A)
  else none

/-- `hardyZApproximantRS₀ t` at `t = tn/td`, to about `ν/W`. -/
def approx₀ (tab : TermTable) (tn td W : Nat) : Option Encl :=
  (approxPartsAt tab tn td W).bind fun (_, A) => approx₀Of A (dyadic W)

/-- `hardyZApproximantRS t` at `t = tn/td`, to about `ν/W`. -/
def approx₁ (tab : TermTable) (tn td W : Nat) : Option Encl :=
  (approxPartsAt tab tn td W).bind fun (_, A) => approx₁Of A (dyadic W)

/-- `hardyZErrorBoundRS₀ t` at `t = tn/td`, along `BSN.hardyZErrorBoundRS₀_mk`:
`25/4·(qT)⁻¹ + 1/32·((qT)³)⁻¹ + 13/10·(q³)⁻¹` with `q = √√T`. -/
def errBoundWith (tn td Q : Nat) : Option Encl :=
  if Nat.ble 1 tn && Nat.ble 1 td then
    (tDivTwoPi tn td Q).bind fun T =>
    (T.sqrt Q).bind fun s =>
    (s.sqrt Q).bind fun q =>
    (Encl.mulR q T Q).bind fun qT =>
    (qT.inv Q).bind fun i₁ =>
    (Encl.mulR qT qT Q).bind fun m₂ =>
    (Encl.mulR m₂ qT Q).bind fun m₃ =>
    (m₃.inv Q).bind fun i₂ =>
    (Encl.mulR q q Q).bind fun r₂ =>
    (Encl.mulR r₂ q Q).bind fun r₃ =>
    (r₃.inv Q).bind fun i₃ =>
    (Encl.mulR (Encl.const false 25 4) i₁ Q).bind fun a₁ =>
    (Encl.mulR (Encl.const false 1 32) i₂ Q).bind fun a₂ =>
    (Encl.mulR (Encl.const false 13 10) i₃ Q).bind fun a₃ =>
    (Encl.addR a₁ a₂ Q).bind fun s₁ =>
    Encl.addR s₁ a₃ Q
  else none

/-- `hardyZErrorBoundRS₀ t` at `t = tn/td`, on the grid `1/dyadic W`. -/
def errBound (tn td W : Nat) : Option Encl := errBoundWith tn td (dyadic W)

/-- `hardyZErrorBoundRS t` at `t = tn/td`, along `BSN.hardyZErrorBoundRS_mk`:
`25/4·(qT)⁻¹ + 1/32·((qT)³)⁻¹` with `q = √√T`. -/
def errBound₁With (tn td Q : Nat) : Option Encl :=
  if Nat.ble 1 tn && Nat.ble 1 td then
    (tDivTwoPi tn td Q).bind fun T =>
    (T.sqrt Q).bind fun s =>
    (s.sqrt Q).bind fun q =>
    (Encl.mulR q T Q).bind fun qT =>
    (qT.inv Q).bind fun i₁ =>
    (Encl.mulR qT qT Q).bind fun m₂ =>
    (Encl.mulR m₂ qT Q).bind fun m₃ =>
    (m₃.inv Q).bind fun i₂ =>
    (Encl.mulR (Encl.const false 25 4) i₁ Q).bind fun a₁ =>
    (Encl.mulR (Encl.const false 1 32) i₂ Q).bind fun a₂ =>
    Encl.addR a₁ a₂ Q
  else none

/-- `hardyZErrorBoundRS t` at `t = tn/td`, on the grid `1/dyadic W`. -/
def errBound₁ (tn td W : Nat) : Option Encl := errBound₁With tn td (dyadic W)

/-! ### The linear-free approximant in fixed point -/

/-- `Ψ(p) = (cos 2πp)⁻¹·cos 2π(p² − p − 1/16)` at `p` enclosed by `P`; `TP` encloses `2π`. Near
`p = 1/4` or `3/4` both factors of the product are far from `1` (`(cos 2πp)⁻¹` large, `cos φ` near
`0`), so it is taken by `Fx.mulExact`. -/
def corrF (tab : TermTable) (H TP P : Fx) : Option Fx :=
  (Fx.cosSinT tab.Q H tab.trig (Fx.mul tab.Q TP P)).bind fun CS =>
  (Fx.inv tab.Q CS.1).bind fun iC =>
  (Fx.cosSinT tab.Q H tab.trig (Fx.mul tab.Q TP
    (Fx.sub (Fx.sub (Fx.mul tab.Q P P) P) (Fx.ofRat false 1 16 tab.Q)))).map fun cs =>
  Fx.mulExact tab.Q iC cs.1

/-- `(−1)^ν·x` from an enclosure of `x`. -/
def signPow (ν : Nat) (X : Fx) : Fx := if ν % 2 == 1 then Fx.neg X else X

/-- `hardyZApproximantRS₀ t = 2·∑ − (−1)^ν·T^{−1/4}·Ψ(p)` at `t = tn/td` with cutoff `ν`
(`BSN.hardyZApproximantRS₀_eq`), on the table's grid. -/
def approx₀FWith (tab : TermTable) (tn td W ν : Nat) (H TP ITP lp : Fx) : Option Fx :=
  (thetaF tn td W tab.Q (thetaConsts tn td) H lp).bind fun θ =>
  (mainSumF θ tn td tab W ν).bind fun S =>
  (Fx.sqrt tab.Q (Fx.mul tab.Q (Fx.ofRat false tn td tab.Q) ITP)).bind fun sqT =>
  (Fx.sqrt tab.Q sqT).bind fun q =>
  (Fx.inv tab.Q q).bind fun iq =>
  (corrF tab H TP (Fx.sub sqT (Fx.ofInt tab.Q ν))).map fun ψ =>
  Fx.sub (Fx.add S S) (Fx.mul tab.Q (signPow ν iq) ψ)

/-- `hardyZApproximantRS₀ t` at `t = tn/td`, as an `Encl`. -/
def approx₀F (tab : TermTable) (tn td W : Nat) : Option Encl :=
  if endpointPos tn td then
    (cutoff tn td).bind fun ν =>
    tab.H.bind fun H => tab.tp.bind fun TP => tab.itp.bind fun ITP => tab.logPiF.bind fun lp =>
    (approx₀FWith tab tn td W ν H TP ITP lp).map (Fx.toEncl tab.Q)
  else none

end Native
