module

public import Enclosure.BinarySplit.Functions.Log2
public import Enclosure.BinarySplit.Tactic.Log
public import Enclosure.BinarySplit.Tactic.Engine

/-!
# High-precision `log 2` metaprograms and shared constants

The metaprogram side of `Functions.Log2`: the Machin factor builders, `mkLog2Proof`, the
`log2_approx%` value elaborator and `log2_near%` enclosure elaborator, the value-only `log2ValAt`,
and the reusable named `log 2` constants (15 dp and 50 dp, each kernel-checked once) in both the
whole-`ℚ` form and the split form the interval `log` reduction consumes.
-/
@[expose] public section


namespace BSN
open Enclosure

open Lean Elab Term Meta in
/-- Build the proof for the Machin factor `log((v+1)/(v-1))` (i.e. `artanh(1/v)`, a unit numerator)
at precision `1/D` via `mkLogPos 1 v D` (its denominator is
`dyadicDenom D`, equal to the shared `Q` from `log2QD`). Returns `(p, proof)`. -/
private meta def mkLogFactor (v D : ℕ) : MetaM (ℕ × Expr × Expr) := do
  let (app, p, Q) ← mkLogPos 1 v D
  -- `mkLogPos 1 v D` concludes `Real.IsNear (Real.log (↑(v+1)/↑(v−1))) false p Q 1 D`.
  let ty := mkIsNearTy (mkRealFn ``Real.log (mkCastDivR (v + 1) (v - 1))) false p Q 1 D
  return (p, ty, app)

/-- The shared denominator and precision for `log 2` to `1/E`: `Q = 2^k` the least
power of two with `2·(15E) ≤ Q`, and `D = 15E` (each factor is certified to `1/D`). -/
private meta def log2QD (E : ℕ) : ℕ × ℕ :=
  let D := 15 * E
  (2 ^ Nat.clog 2 (2 * D), D)

open Lean Elab Term Meta in
/-- Shared core: `(P, Q, proof)` with `proof : Real.IsNear (Real.log 2) false P Q 1 E`, the dyadic
`P/Q` from the Machin decomposition (`Q = 2^k`, `P = 7p₁+5p₂+3p₃`, passed as a literal tied by
`Nat.beq`). Public so the `exp` `log 2` range-reduction tactic can build a `log 2` certificate at
chosen precision. -/
meta def mkLog2Proof (E : ℕ) : MetaM (ℕ × ℕ × Expr) := do
  let (Q, D) := log2QD E
  let (p₁, t₁, h₁) ← mkLogFactor 31 D
  let (p₂, t₂, h₂) ← mkLogFactor 49 D
  let (p₃, t₃, h₃) ← mkLogFactor 161 D
  -- Lift each factor proof to its own auxiliary lemma so the combined term stays small
  -- (no monolithic inlined proof to re-hash; this is what keeps `maxSharing` cheap).
  let c₁ ← mkBoundAux t₁ h₁
  let c₂ ← mkBoundAux t₂ h₂
  let c₃ ← mkBoundAux t₃ h₃
  let P := 7 * p₁ + 5 * p₂ + 3 * p₃
  let app := mkAppN (mkConst ``log2_combine)
    #[natLitShared p₁, natLitShared p₂, natLitShared p₃, natLitShared Q, natLitShared D,
      natLitShared E, natLitShared P,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, c₁, c₂, c₃]
  return (P, Q, app)

open Lean Elab Term Meta in
/-- Value-only dyadic numerator for the factor `log((v+1)/(v−1))` at denominator `Q`, via the
value core `logCore 1 v D` (its denominator `dyadicDenom D` equals the shared `Q`). -/
private meta def mkLogFactorVal (v D : ℕ) : MetaM ℕ := do
  let (p, _, _, _) ← logCore 1 v D
  return p

open Lean Elab Term Meta in
/-- `log2_approx% E : ℚ` is the dyadic rational `P/Q` approximating `log 2` to `1/E`, as a
plain `ℚ` value (no proof). Its companion `IsNear` enclosure is `log2_near%`. -/
elab "log2_approx% " En:num : term => do
  let (Q, D) := log2QD En.getNat
  let P := 7 * (← mkLogFactorVal 31 D) + 5 * (← mkLogFactorVal 49 D)
    + 3 * (← mkLogFactorVal 161 D)
  mkNatDyadic P Q

open Lean Elab Term Meta in
/-- Value-only `log 2 ≈ P/Q` to precision `1/E` (no proof), for the `exp` range-reduction tactic's
cheap `k = ⌊X/log 2⌋` computation. -/
meta def log2ValAt (E : ℕ) : MetaM (ℕ × ℕ) := do
  let (Q, D) := log2QD E
  let P := 7 * (← mkLogFactorVal 31 D) + 5 * (← mkLogFactorVal 49 D)
    + 3 * (← mkLogFactorVal 161 D)
  return (P, Q)

open Lean Elab Term Meta in
/-- The dyadic numerator of `log 2 ≈ P/Q` at precision `1/E`, as a literal. -/
elab "log2Num% " En:num : term => do return natLitShared (← log2ValAt En.getNat).1

open Lean Elab Term Meta in
/-- The dyadic denominator (`2^k`) of `log 2 ≈ P/Q` at precision `1/E`, as a literal. -/
elab "log2Den% " En:num : term => do return natLitShared (← log2ValAt En.getNat).2

open Lean Elab Term Meta in
/-- `log2_near% E` : the Machin `IsNear` enclosure of `log 2` (centre `P/Q`, radius `1/E`),
as a proof term. Used to state the reusable fixed-precision constants below. -/
elab "log2_near% " En:num : term => do
  let (_, _, pf) ← mkLog2Proof En.getNat
  return pf

/-! ### Reusable named `log 2` constants

Fixed-precision `IsNear` enclosures of `log 2`, each kernel-checked once. The interval `log`
range reduction (`log_rat_reduce_isNear`), the `exp` `log 2` reduction, and `log2_near%`
all reference these instead of rebuilding the Machin certificate per call. -/

/-- `log 2` to `1/10¹⁵` as an `IsNear` enclosure with literal dyadic fields; the 15-dp shared
`log 2` constant, kernel-checked once. -/
theorem log2_near_15 :
    Real.IsNear (Real.log 2) false (log2Num% 1000000000000000) (log2Den% 1000000000000000)
      1 1000000000000000 :=
  log2_near% 1000000000000000

/-- `log 2` to `1/10⁵⁰` as an `IsNear` enclosure with literal dyadic fields; the 50-dp shared
`log 2` constant, kernel-checked once. -/
theorem log2_near_50 :
    Real.IsNear (Real.log 2)
      false (log2Num% 100000000000000000000000000000000000000000000000000)
      (log2Den% 100000000000000000000000000000000000000000000000000)
      1 100000000000000000000000000000000000000000000000000 :=
  log2_near% 100000000000000000000000000000000000000000000000000

open Lean Elab Term Meta in
/-- Pick a cached `log 2` tier for a needed precision `1/E` (`E ≤ 10⁵⁰`). Returns
`(Euse, p2, Q2, proof)` with `proof : Real.IsNear (Real.log 2) false p2 Q2 1 Euse`. With
`weaken := true` and the nearest tier at least three bits finer than `E`, the tier is recentred
once (`mkWeakenedNear`) to radius `1/(4E)` with ~`log₂ E`-bit fields; this pays only for a
`weaken := true` caller. Composing sites take the default `weaken := false` and use the tier as is.
`none` above the 10⁵⁰ tier. -/
meta def mkLog2Tier? (E : ℕ) (weaken : Bool := false) : MetaM (Option (ℕ × ℕ × ℕ × Expr)) := do
  let some (T, name) :=
      if E ≤ 10 ^ 15 then some (10 ^ 15, ``log2_near_15)
      else if E ≤ 10 ^ 50 then some (10 ^ 50, ``log2_near_50)
      else none
    | return none
  let (pt, Qt) ← log2ValAt T
  if weaken && 8 * E ≤ T then
    let (proof, p2,
         Q2) ← mkWeakenedNear name (mkRealFn ``Real.log mkRealTwo) false pt Qt 1 T (4 * E)
    return some (4 * E, p2, Q2, proof)
  else
    return some (T, pt, Qt, mkConst name)

end BSN
