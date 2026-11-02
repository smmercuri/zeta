module

public import Zeta.Zeros.Certificates.Basic
public import Zeta.Certificate.NamedRS
public import Enclosure.BinarySplit.Tactic.Recognizer
public import Zeta.Zeros.BuildCerts
public meta import Zeta.Certificate.NamedRS

/-!
# Build the Riemann-Siegel zero certificates directly from the data file

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
in the store is an error instead of a silently shifted batch. -/
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

/-- One bracket plus its Euler–Maclaurin parameters, again fully explicit; see `mkNEI`. -/
def mkZIRS (a b : ℝ) (h : a ≤ b) : ZIntervalRS := mkNEI a b h

/-- The left endpoint value of a `mkZIRS` interval is `hardyZApproximantRS` at its left endpoint.
Lets `buildCertRS` transport the cached enclosure onto the `ZIntervalRS.fstVal` subject through a
cited equality rather than a `mkReflR` defeq that re-unfolds the wrapper at every row. -/
theorem fstVal_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.fstVal (mkZIRS a b h) = hardyZApproximantRS a := rfl

/-- The right endpoint value of a `mkZIRS` interval is `hardyZApproximantRS` at its right endpoint;
the companion of `fstVal_mkZIRS`. -/
theorem sndVal_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.sndVal (mkZIRS a b h) = hardyZApproximantRS b := rfl

/-- `fstVal_mkZIRS` for the linear-free approximant. -/
theorem fstVal₀_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.fstVal₀ (mkZIRS a b h) = hardyZApproximantRS₀ a := rfl

/-- `sndVal_mkZIRS` for the linear-free approximant. -/
theorem sndVal₀_mkZIRS (a b : ℝ) (h : a ≤ b) :
    ZIntervalRS.sndVal₀ (mkZIRS a b h) = hardyZApproximantRS₀ b := rfl

/-- The `fst_le_snd` reflection proof for one row's endpoints. -/
meta def buildLeSndRS (r : RowRS) : MetaM Expr := do
  let leftE ← ofSciReal r.lm r.ldp
  let rightE ← ofSciReal r.rm r.rdp
  return mkAppN (mkConst ``Enclosure.dec_le_dec)
    #[leftE, rightE, mkNatLit r.lm, mkNatLit (10 ^ r.ldp), mkNatLit r.rm, mkNatLit (10 ^ r.rdp),
      sfracEq r.lm r.ldp, sfracEq r.rm r.rdp, BSN.reflBoolTrue, BSN.reflBoolTrue, BSN.reflBoolTrue]

/-- The bare `NonemptyInterval ℝ` for one row: the endpoint pair plus `fst_le_snd`. This is what
the bundle actually stores — `ZIntervalEM`'s cutoff/Bernoulli parameters exist only to state the
certificate. -/
meta def buildNonemptyIntervalRS (r : RowRS) : MetaM Expr := do
  return mkAppN (mkConst ``mkNEI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← buildLeSndRS r]

/-- Build the `ZIntervalRS` term for one row: the `NonemptyInterval` it abbreviates. -/
meta def buildIntervalRS (r : RowRS) : MetaM Expr := do
  return mkAppN (mkConst ``mkZIRS)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← buildLeSndRS r]

/-- Working precision a single row's bracket needs: `base / width`, floored.
`base = 1e5·max(1,t/30)` is the flat value that certifies at width ~1; wider brackets need less
precision, narrower ones more. Width is `(rm·10^ldp − lm·10^rdp)/10^(ldp+rdp)`, so
`D = base·10^(ldp+rdp)/wnum`. (#146) The floor is `10000·t30²` (quadratic, not linear): the
precision needed to keep `|Z|`'s magnitude enclosure off zero grows faster than linearly in height,
so a linear floor under-provisions wide high-t brackets (they straddle zero); `t30²` gives ~1e4 at
low t (unchanged) but ~2e7 at t≈1400. -/
meta def drow0RS (r : RowRS) : Nat :=
  let t30 := max 1 (r.lm / (30 * 10 ^ r.ldp))
  let wnum := max 1 (r.rm * 10 ^ r.ldp - r.lm * 10 ^ r.rdp)
  max (10000 * t30 * t30) (100000 * t30 * 10 ^ (r.ldp + r.rdp) / wnum)

/-- A batch's working precision: the largest `drow0RS` over its rows. The native pre-check
(`build_batch_rs +native`) evaluates at this same precision, so a batch it accepts is one the
kernel metaprogram is expected to certify. -/
meta def batchPrecRS (rows : Array RowRS) : Nat := rows.foldl (fun acc r => max acc (drow0RS r)) 1

/-- Build one row's certificate proof term at working precision `D` (chosen once per chunk by
`buildBundle`, so every row shares the `D`-keyed enclosure caches): the mechanical reflection
fields, plus the three heavy fields (`is_sign_change`, `fst_error`, `snd_error`) delegated to the
hardy cores. With `withC₁` it is a `ZIntervalRS.Certificate`, otherwise a `ZIntervalRS.Certificate₀`
(no `C₁` enclosure, larger error bound); the hardy cores throw if a margin or the sign change
fails. -/
meta def buildCertRS (r : RowRS) (D : Nat) (withC₁ : Bool) (lo : Nat × Nat) : MetaM Expr := do
  let leftE ← ofSciReal r.lm r.ldp
  let rightE ← ofSciReal r.rm r.rdp
  let hle ← buildLeSndRS r
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
`precisionRetriesRS`. Only a failing row uses them, and Lake never caches a failed batch, so the
value need not be part of any batch's trace. -/
meta def retriesRS : IO Nat :=
  return ((← IO.getEnv "ZETA_RS_RETRIES").bind String.toNat?).getD precisionRetriesRS

/-- The factor a failing row's working precision is raised by on each retry. -/
meta def precisionStepRS : Nat := 100

/-- One row's `ZIntervalRS.Certified` proof: the linear-free `Certificate₀` when both endpoint
values clear its larger error bound (no `C₁` enclosure to build or check), else the full
`Certificate`. The fallback is recorded as a `BSN.phases` trace node, so a profile counts it.

The batch's working precision `D` is a heuristic in the height, and an endpoint very close to a
zero can need more: if neither certificate builds at `D`, the row alone is retried at
`precisionStepRS · D`, up to `retries` times (rows that pass are unaffected), and the last failure
is reported. -/
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
  try attempt D
  catch err =>
    let mut err := err
    let mut D := D
    for _ in [0:retries] do
      D := D * precisionStepRS
      try return ← BSN.withPhase s!"RS: raise precision to {D}" (attempt D)
      catch e => err := e
    throw err

/-- The element type of the list `ofCertifiedRS` consumes, named so the metaprogram can cite it
as a constant rather than rebuilding the `PSigma` binder. -/
abbrev CertPairRS := Σ' I : ZIntervalRS, I.Certified

private meta def certPairRSE : Expr := mkConst ``CertPairRS

/-- `⟨I, cert⟩ : CertPairRS`, built with the dependent second component `β := ZIntervalRS.Certified`
supplied explicitly. `mkAppM` cannot be used here: it would infer the *constant* family
`fun _ ↦ I.Certified` from the type of `cert`, which is not the `Σ' I, I.Certified` the bundle
is indexed by. -/
meta def mkCertPairRS (I cert : Expr) : Expr :=
  mkAppN (Expr.const ``PSigma.mk [Level.succ Level.zero, Level.zero])
    #[mkConst ``ZIntervalRS, mkConst ``ZIntervalRS.Certified, I, cert]

private meta def chainRelE : Expr := mkConst ``chainRel
private meta def neiE : Expr := mkConst ``NEInterval

/-- `[⟨intervalᵢ, certᵢ⟩, …] : List CertPair` for rows `i…` as a literal cons `Expr`. This is the
list `ofCertifiedEM` takes; the certificates ride along inside it, so there is no separate
`∀ I ∈ …, I.Certificate` field to build. -/
meta partial def buildPairsFromRS (rows : Array RowRS) (i : Nat) (D : Nat) (lo : Nat × Nat)
    (retries : Nat) : MetaM Expr := do
  if h : i < rows.size then
    -- each row is its own certificate, so each gets the default `maxHeartbeats` budget rather than
    -- sharing one across the batch (whose total grows with the height)
    let cert ← withCurrHeartbeats (buildCertifiedRS rows[i] D lo retries)
    let pair := mkCertPairRS (← buildIntervalRS rows[i]) cert
    return mkApp3 (Expr.const ``List.cons [Level.zero]) certPairRSE pair
      (← buildPairsFromRS rows (i + 1) D lo retries)
  else
    return mkApp (Expr.const ``List.nil [Level.zero]) certPairRSE

/-- Proof of `[intervalᵢ.toNonemptyInterval, …].IsChain chainRel` by passing
right-to-left. -/
meta partial def buildDisjRS (rows : Array RowRS) : MetaM Expr := do
  let nei := neiE
  let neis ← rows.mapM buildNonemptyIntervalRS
  let n := neis.size
  if n == 0 then return mkAppN (Expr.const ``List.IsChain.nil [Level.zero]) #[nei, chainRelE]
  let mut tl := mkApp (Expr.const ``List.nil [Level.zero]) nei
  let mut pf := mkAppN (Expr.const ``List.IsChain.singleton [Level.zero])
    #[nei, chainRelE, neis[n - 1]!]
  for j in [0:n - 1] do
    let i := n - 2 - j
    let lePf ← decLeDec rows[i]!.rm rows[i]!.rdp rows[i + 1]!.lm rows[i + 1]!.ldp
    pf := mkAppN (Expr.const ``List.IsChain.cons_cons [Level.zero])
      #[nei, chainRelE, neis[i]!, neis[i + 1]!, tl, lePf, pf]
    tl := mkApp3 (Expr.const ``List.cons [Level.zero]) nei neis[i + 1]! tl
  return pf

/-- Build the whole `CertifiedZeroIntervals` bundle (intervals + certs + disj) from the rows.
Working precision is ONE value per chunk: the max over its rows of `drow0`. Every row then gets at
least the precision its own bracket width needs (so all margins pass), while a single `D` keeps the
`D`-keyed enclosure caches (`piVal`/`log`/`√`/`trigReduce`) shared across the chunk — cache sharing
dominates the per-row precision saving, and this is the LOWEST `D` that preserves that sharing.
(#146) -/
meta def buildBundleRS (rows : Array RowRS) (retries : Nat := precisionRetriesRS) :
    MetaM Expr := do
  let chunkD := batchPrecRS rows
  -- the batch's lowest endpoint: its error bound is enclosed once and shared by every endpoint
  let lo := rows[0]?.elim (1, 1) fun r => (r.lm, 10 ^ r.ldp)
  return mkAppN (mkConst ``CertifiedZeroIntervals.ofCertifiedRS)
    #[← buildPairsFromRS rows 0 chunkD lo retries, ← withCurrHeartbeats (buildDisjRS rows)]

/-- The Riemann-Siegel zero store `gen_zero_certificates.py` reads from, its rows in the same
`idx, fst, snd` layout `parseRowsRS` expects. -/
meta def storeDirRS : System.FilePath := "python/out/riemann_siegel/zeros"

open Elab Tactic in
/-- `build_certs lo hi` closes a `CertifiedZeroIntervals` goal by building the bundle directly
from rows `[lo, hi)` of the data file — no named declarations, no `fin_cases`. -/
elab "build_certs_rs " lo:num hi:num : tactic => do
  let rows ← match parseRowsRS (← storeLines storeDirRS lo.getNat hi.getNat) lo.getNat with
    | .ok rows => pure rows
    | .error msg => throwError msg
  let e ← buildBundleRS rows
  liftMetaFinishingTactic (·.assign e)

open Elab Tactic in
/-- `build_batch_rs lo hi` closes a `BatchSpec` goal from rows `[lo, hi)` of the Riemann–Siegel
store; see `build_batch`. A failing row's working precision is raised up to `retriesRS` times. -/
elab "build_batch_rs " lo:num hi:num : tactic => do
  let retries ← retriesRS
  let rows ← match parseRowsRS (← storeLines storeDirRS lo.getNat hi.getNat) lo.getNat with
    | .ok rows => pure rows
    | .error msg => throwError msg
  let e ← buildBundleRS rows retries
  -- the assembly gets its own default budget too, as each row's certificate does
  liftMetaFinishingTactic fun g => withCurrHeartbeats (closeBatchSpec e g)

end Zeta.Certificates
