/-
Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Bhavik Mehta
-/
module

public import Zeta.Zeros.Certificates.Basic
public import Zeta.Certificate.NamedRS
public import Enclosure.BinarySplit.Tactic.Recognizer
public import Zeta.Zeros.BuildCerts
public meta import Zeta.Certificate.NamedRS

/-!
# Build the Riemann–Siegel zero certificates directly from the data file

The Riemann–Siegel counterpart of `Zeta.Zeros.BuildCerts`: `build_certs_rs` and `build_batch_rs`
build a `CertifiedZeroIntervals` bundle of `ZIntervalRS.Certified` pairs from rows of the
Riemann–Siegel zero store, with the heavy fields delegated to `Zeta.Certificate.NamedRS`.
-/
@[expose] public section

open Lean Elab Term Meta

namespace Zeta.Certificates

/-- One parsed data row: endpoints as (mantissa, decimal places). -/
meta structure RowRS where
  lm : Nat
  ldp : Nat
  rm : Nat
  rdp : Nat
deriving Inhabited

/-- Parse `lines`, rows `[lo, …)` of the store (see `storeLines`). Row `k` (0-based) is located by
position, then checked against its own leading index column (`k + 1`), so a header line or a gap
in the store raises an error. -/
meta def parseRowsRS (lines : Array String) (lo : Nat) : Except String (Array RowRS) := do
  let mut rows : Array RowRS := #[]
  let mut k := lo
  for line in lines do
    let [idx, l, r] := (line.replace " " "").splitOn ","
      | throw s!"store row {k + 1}: expected 3 columns, got `{line}`"
    unless idx.toNat? == some (k + 1) do
      throw s!"store row {k + 1}: index column reads `{idx}`"
    let (lm, ldp) := parseDec l
    let (rm, rdp) := parseDec r
    rows := rows.push { lm, ldp, rm, rdp }
    k := k + 1
  return rows

/-- One Riemann–Siegel bracket, with every argument explicit; see `mkNEI`. -/
def mkZIRS (a b : ℝ) (h : a ≤ b) : ZIntervalRS := mkNEI a b h

/-- The left endpoint value of a `mkZIRS` interval is `hardyZApproximantRS` at its left endpoint
(cited instead of a defeq that re-unfolds the wrapper at every row). -/
theorem fstVal_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.fstVal (mkZIRS a b h) = hardyZApproximantRS a := rfl

/-- The right endpoint value of a `mkZIRS` interval is `hardyZApproximantRS` at its right
endpoint. -/
theorem sndVal_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.sndVal (mkZIRS a b h) = hardyZApproximantRS b := rfl

/-- `fstVal_mkZIRS` for the linear-free approximant. -/
theorem fstVal₀_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.fstVal₀ (mkZIRS a b h) = hardyZApproximantRS₀ a := rfl

/-- `sndVal_mkZIRS` for the linear-free approximant. -/
theorem sndVal₀_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.sndVal₀ (mkZIRS a b h) = hardyZApproximantRS₀ b := rfl

/-- The bare `NonemptyInterval ℝ` for one row: the endpoint pair plus `fst_le_snd`. -/
meta def buildNonemptyIntervalRS (r : RowRS) : MetaM Expr := do
  return mkAppN (mkConst ``mkNEI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← decLeDec r.lm r.ldp r.rm r.rdp]

/-- Build the `ZIntervalRS` term for one row: the `NonemptyInterval` it abbreviates. -/
meta def buildIntervalRS (r : RowRS) : MetaM Expr := do
  return mkAppN (mkConst ``mkZIRS)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← decLeDec r.lm r.ldp r.rm r.rdp]

/-- A batch's working precision: the largest `rowPrecision` over its rows. The native pre-check
uses the same precision, so a batch it accepts is one the kernel metaprogram is expected to
certify. -/
meta def batchPrecRS (rows : Array RowRS) : Nat :=
  rows.foldl (fun acc r ↦ max acc (rowPrecision r.lm r.ldp r.rm r.rdp)) 1

/-- One row's certificate proof term at working precision `D`: a `ZIntervalRS.Certificate` with
`withC₁`, otherwise a `ZIntervalRS.Certificate₀` (no `C₁` enclosure, larger error bound). Throws
if a margin or the sign change fails. -/
meta def buildCertRS (r : RowRS) (D : Nat) (withC₁ : Bool) (lo : Nat × Nat) : MetaM Expr := do
  let leftE ← ofSciReal r.lm r.ldp
  let rightE ← ofSciReal r.rm r.rdp
  let hle ← decLeDec r.lm r.ldp r.rm r.rdp
  -- build `I` from the same endpoint/`≤` terms the sites carry, so the `fstVal`/`sndVal` renames
  -- below match `I` syntactically (matches `buildIntervalRS r`, which is deterministic)
  let I := mkAppN (mkConst ``mkZIRS) #[leftE, rightE, hle]
  let leFst := mkAppN (mkConst ``BSN.thirtyTwoPi_le_dec)
    #[leftE, mkNatLit r.lm, mkNatLit (10 ^ r.ldp), sfracEq r.lm r.ldp, reflBoolTrue,
      reflBoolTrue]
  let (fstV, sndV, fstEq, sndEq, bound, mk) := if withC₁ then
      (``ZIntervalRS.fstVal, ``ZIntervalRS.sndVal, ``fstVal_mkZIRS, ``sndVal_mkZIRS,
        ``hardyZErrorBoundRS, ``ZIntervalRS.Certificate.mk)
    else
      (``ZIntervalRS.fstVal₀, ``ZIntervalRS.sndVal₀, ``fstVal₀_mkZIRS, ``sndVal₀_mkZIRS,
        ``hardyZErrorBoundRS₀, ``ZIntervalRS.Certificate₀.mk)
  let siteL : BSN.HardyZSiteRS :=
    { x := mkApp (mkConst fstV) I,
      tn := r.lm, td := 10 ^ r.ldp, htE := sfracEq r.lm r.ldp, tE := leftE,
      he := mkAppN (mkConst fstEq) #[leftE, rightE, hle] }
  let siteR : BSN.HardyZSiteRS :=
    { x := mkApp (mkConst sndV) I,
      tn := r.rm, td := 10 ^ r.rdp, htE := sfracEq r.rm r.rdp, tE := rightE,
      he := mkAppN (mkConst sndEq) #[leftE, rightE, hle] }
  let signChange ← BSN.hardySignChangeSitesRS siteL siteR (some D) withC₁
  let leftErr ← BSN.hardyErrOkSiteRS siteL (mkApp (mkConst bound) leftE) (some D) withC₁ lo
  let rightErr ← BSN.hardyErrOkSiteRS siteR (mkApp (mkConst bound) rightE) (some D) withC₁ lo
  return mkAppN (mkConst mk) #[I, leFst, signChange, leftErr, rightErr]

/-- How many times `buildCertifiedRS` multiplies a failing row's working precision by
`precisionStepRS` before giving up, unless `build.sh --retries k` asks for more (`retriesRS`). -/
meta def precisionRetriesRS : Nat := 3

/-- The retries for this build: `ZETA_RS_RETRIES` (set by `build.sh --retries k`), else
`precisionRetriesRS`. Lake never caches a failed batch, so the value need not be in any trace. -/
meta def retriesRS : IO Nat :=
  return ((← IO.getEnv "ZETA_RS_RETRIES").bind String.toNat?).getD precisionRetriesRS

/-- The factor a failing row's working precision is raised by on each retry. -/
meta def precisionStepRS : Nat := 100

/-- One row's `ZIntervalRS.Certified` proof: the linear-free `Certificate₀` when both endpoint
values clear its larger error bound, else the full `Certificate`. If neither builds at `D`, the row
alone is retried at `precisionStepRS · D` up to `retries` times; the last failure is reported. -/
meta def buildCertifiedRS (r : RowRS) (D : Nat) (lo : Nat × Nat) (retries : Nat) :
    MetaM Expr := do
  let I ← buildIntervalRS r
  let cert := mkApp (mkConst ``ZIntervalRS.Certificate) I
  let cert₀ := mkApp (mkConst ``ZIntervalRS.Certificate₀) I
  let attempt (D : Nat) : MetaM Expr := do
    try
      return mkApp3 (mkConst ``Or.inr) cert cert₀ (← buildCertRS r D false lo)
    catch _ =>
      BSN.withPhase "RS: fall back to C₁" do
        return mkApp3 (mkConst ``Or.inl) cert cert₀ (← buildCertRS r D true lo)
  withPrecisionRetries "RS" precisionStepRS D retries attempt

/-- The element type of the list `ofCertifiedRS` consumes, named so the metaprogram can cite it
as a constant. -/
abbrev CertPairRS := Σ' I : ZIntervalRS, I.Certified

private meta def certPairRSE : Expr := mkConst ``CertPairRS

/-- `⟨I, cert⟩ : CertPairRS`, with the family `β := ZIntervalRS.Certified` explicit (`mkAppM`
would infer the constant family `fun _ ↦ I.Certified`). -/
meta def mkCertPairRS (I cert : Expr) : Expr :=
  mkAppN (Expr.const ``PSigma.mk [Level.succ Level.zero, Level.zero])
    #[mkConst ``ZIntervalRS, mkConst ``ZIntervalRS.Certified, I, cert]

/-- The whole `CertifiedZeroIntervals` bundle for the rows, at one working precision per batch
(`batchPrecRS`) so its rows hit the same `D`-keyed enclosure caches. -/
meta def buildBundleRS (rows : Array RowRS) (retries : Nat := precisionRetriesRS) :
    MetaM Expr := do
  let chunkD := batchPrecRS rows
  -- the batch's lowest endpoint: its error bound is enclosed once and shared by every endpoint
  let lo := rows[0]?.elim (1, 1) fun r ↦ (r.lm, 10 ^ r.ldp)
  let pairs ← buildListFrom certPairRSE rows (fun r ↦ do
    -- each row is its own certificate, so each gets the default `maxHeartbeats` budget rather than
    -- sharing one across the batch (whose total grows with the height)
    let cert ← withCurrHeartbeats (buildCertifiedRS r chunkD lo retries)
    return mkCertPairRS (← buildIntervalRS r) cert) 0
  let disj ← withCurrHeartbeats <|
    buildChain rows buildNonemptyIntervalRS fun a b ↦ decLeDec a.rm a.rdp b.lm b.ldp
  return mkAppN (mkConst ``CertifiedZeroIntervals.ofCertifiedRS) #[pairs, disj]

/-- The Riemann–Siegel zero store `gen_zero_certificates.py` reads from, its rows in the same
`idx, fst, snd` layout `parseRowsRS` expects. -/
meta def storeDirRS : System.FilePath := "python/out/riemann_siegel/zeros"

open Elab Tactic in
/-- `build_certs_rs lo hi` closes a `CertifiedZeroIntervals` goal with the bundle built from rows
`[lo, hi)` of the Riemann–Siegel store. -/
elab "build_certs_rs " lo:num hi:num : tactic => do
  let rows ← ofExcept <| parseRowsRS (← storeLines storeDirRS lo.getNat hi.getNat) lo.getNat
  let e ← buildBundleRS rows
  liftMetaFinishingTactic (·.assign e)

open Elab Tactic in
/-- `build_batch_rs lo hi` closes a `BatchSpec` goal from rows `[lo, hi)` of the Riemann–Siegel
store; see `build_batch`. A failing row's working precision is raised up to `retriesRS` times. -/
elab "build_batch_rs " lo:num hi:num : tactic => do
  let retries ← retriesRS
  let rows ← ofExcept <| parseRowsRS (← storeLines storeDirRS lo.getNat hi.getNat) lo.getNat
  let e ← buildBundleRS rows retries
  -- the assembly gets its own default budget too, as each row's certificate does
  liftMetaFinishingTactic fun g ↦ withCurrHeartbeats (closeBatchSpec e g)

end Zeta.Certificates
