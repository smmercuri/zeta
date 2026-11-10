/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Zeta.Zeros.Certificates.Basic
public import Zeta.Certificate.Named
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Zeta.Certificate.Named

/-!
# Build the Euler–Maclaurin zero certificates directly from the data file

`build_certs lo hi` reads rows `[lo, hi)` of the zero store and emits a whole
`CertifiedZeroIntervals` as one `Expr` (the intervals, their `ZIntervalEM.Certificate`s and the
disjointness chain), so a batch module is a single line and the bracket numbers live only in the
data file. `build_batch` closes a `BatchSpec` the same way.

The heavy fields (`is_sign_change`, `fst_error`, `snd_error`) are delegated to the cores in
`Zeta.Certificate.Named`; everything else is a reflection proof over ℕ literals. The bundle is
assembled through `CertifiedZeroIntervals.ofCertifiedEM` (`Certificates/Basic.lean`), which also
holds the batch-to-batch seams. Endpoints are imported exactly as the store writes them.
-/
@[expose] public section

open Lean Elab Term Meta

namespace Zeta.Certificates

/-- One parsed data row: endpoints as (mantissa, decimal places), plus the four Nat params. -/
structure Row where
  lm : Nat
  ldp : Nat
  rm : Nat
  rdp : Nat
  lco : Nat
  rco : Nat
  lb : Nat
  rb : Nat
deriving Inhabited

/-- Parse a decimal string `"14.13468"` into `(mantissa, decimalPlaces)` = `(1413468, 5)`. -/
meta def parseDec (s : String) : Nat × Nat :=
  match s.splitOn "." with
  | [i, f] => ((i ++ f).toNat!, f.length)
  | [i]    => (i.toNat!, 0)
  | _      => (0, 0)

/-- Rows `[lo, hi)` of the zero store in directory `store`, one line each, read from the files
that `manifest.json` lists as overlapping the range. A file whose line count disagrees with the
manifest, or a range running past the store's end, is an error. -/
meta def storeLines (store : System.FilePath) (lo hi : Nat) : IO (Array String) := do
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile (store / "manifest.json"))
  let files ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "files"
  let mut lines : Array String := #[]
  let mut start := 0
  for f in files do
    let n ← IO.ofExcept <| f.getObjValAs? Nat "rows"
    if lo < start + n && start < hi then
      let path := store / (← IO.ofExcept <| f.getObjValAs? String "file")
      let all := ((← IO.FS.readFile path).splitOn "\n").toArray.filter (!·.isEmpty)
      unless all.size == n do
        throw <| .userError s!"{path}: manifest lists {n} rows, the file has {all.size}"
      lines := lines ++ all.extract (lo - start) (hi - start)
    start := start + n
  unless lines.size == hi - lo do
    throw <| .userError s!"{store}: store has {start} rows; batch wants [{lo}, {hi})"
  return lines

/-- Parse store lines into `Row`s. A data row is a line starting with a digit, of exactly the 7
columns `idx, left, right, lco, rco, lb, rb`; the leading index is dropped. -/
meta def parseRows (lines : Array String) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for line in lines do
    let line := line.replace " " ""
    if line.isEmpty || !line.front.isDigit then continue
    let parts := line.splitOn ","
    if parts.length != 7 then continue
    let parts := parts.drop 1
    let (lm, ldp) := parseDec parts[0]!
    let (rm, rdp) := parseDec parts[1]!
    rows := rows.push
      { lm, ldp, rm, rdp, lco := parts[2]!.toNat!, rco := parts[3]!.toNat!,
        lb := parts[4]!.toNat!, rb := parts[5]!.toNat! }
  return rows

private meta def realTy : Expr := mkConst ``Real

/-- The decimal endpoint `m·10⁻ᵈᵖ` as `sfrac false m (10^dp)`, not `OfScientific.ofScientific`,
so the kernel never reduces it through `Rat.ofScientific`. -/
meta def ofSciReal (m dp : Nat) : MetaM Expr := do
  return mkApp3 (mkConst ``Enclosure.sfrac) (mkConst ``Bool.false) (mkNatLit m) (mkNatLit (10 ^ dp))

/-- The endpoint is already `sfrac false m (10^dp)`, so its `= sfrac …` fact is reflexivity. -/
meta def sfracEq (m dp : Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) realTy
    (mkApp3 (mkConst ``Enclosure.sfrac) (mkConst ``Bool.false) (mkNatLit m) (mkNatLit (10 ^ dp)))

/-- The bundle's element type, named so the metaprogram can cite it without synthesising the
`LE ℝ` instance argument of `NonemptyInterval`. -/
abbrev NEInterval := NonemptyInterval ℝ

/-- One bracket as a `NEInterval`, with every argument explicit (no `LE ℝ` instance to build). -/
def mkNEI (a b : ℝ) (h : a ≤ b) : NEInterval := ⟨(a, b), h⟩

/-- One bracket plus its Euler–Maclaurin parameters, again fully explicit; see `mkNEI`. -/
def mkZI (a b : ℝ) (h : a ≤ b) (fc sc fb sb : ℕ) : ZIntervalEM :=
  ⟨mkNEI a b h, fc, sc, fb, sb⟩

/-- `dec_le_dec` proof that `ofSci(am,adp) ≤ ofSci(bm,bdp)`. -/
meta def decLeDec (am adp bm bdp : Nat) : MetaM Expr := do
  let aE ← ofSciReal am adp
  let bE ← ofSciReal bm bdp
  return mkAppN (mkConst ``Enclosure.dec_le_dec)
    #[aE, bE, mkNatLit am, mkNatLit (10 ^ adp), mkNatLit bm, mkNatLit (10 ^ bdp),
      sfracEq am adp, sfracEq bm bdp, BSN.reflBoolTrue, BSN.reflBoolTrue, BSN.reflBoolTrue]

/-- The bare `NonemptyInterval ℝ` for one row: the endpoint pair plus `fst_le_snd`. -/
meta def buildNonemptyInterval (r : Row) : MetaM Expr := do
  return mkAppN (mkConst ``mkNEI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← decLeDec r.lm r.ldp r.rm r.rdp]

/-- Build the `ZIntervalEM` term for one row: the `NonemptyInterval` it extends, then the four
Euler–Maclaurin parameters in field order (`fstCutoff`, `sndCutoff`, `fstBernoulli`,
`sndBernoulli`). -/
meta def buildInterval (r : Row) : MetaM Expr := do
  return mkAppN (mkConst ``mkZI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← decLeDec r.lm r.ldp r.rm r.rdp,
      mkNatLit r.lco, mkNatLit r.rco, mkNatLit r.lb, mkNatLit r.rb]

/-- Working precision the bracket `[lm·10⁻ˡᵈᵖ, rm·10⁻ʳᵈᵖ]` needs: `1e5·max(1, t/30) / width`, at
least `10000·max(1, t/30)²` (quadratic, since the precision needed to keep `|Z|`'s enclosure off
zero grows faster than linearly in height). -/
meta def rowPrecision (lm ldp rm rdp : Nat) : Nat :=
  let t30 := max 1 (lm / (30 * 10 ^ ldp))
  let wnum := max 1 (rm * 10 ^ ldp - lm * 10 ^ rdp)
  max (10000 * t30 * t30) (100000 * t30 * 10 ^ (ldp + rdp) / wnum)

/-- The `Certificate` proof term for one row at working precision `D`: reflection proofs for the
mechanical fields, the hardy cores for `is_sign_change`, `fst_error` and `snd_error`. -/
meta def buildCert (r : Row) (D : Nat) : MetaM Expr := do
  let I ← buildInterval r
  let leftE ← ofSciReal r.lm r.ldp
  let rightE ← ofSciReal r.rm r.rdp
  let leftNonneg := mkAppN (mkConst ``Enclosure.dec_nonneg)
    #[leftE, mkNatLit r.lm, mkNatLit (10 ^ r.ldp), sfracEq r.lm r.ldp]
  let posPf (n : Nat) : Expr :=
    mkAppN (mkConst ``Enclosure.pos_of_ble) #[mkNatLit n, BSN.reflBoolTrue]
  -- The row already holds every field of a `HardyZSite`, so the sign/error cores take the value
  -- directly; `x` is the subject the corresponding certificate field is stated about.
  let siteL : BSN.HardyZSite :=
    { x := mkApp (mkConst ``ZIntervalEM.fstVal) I, M := r.lb, N := r.lco,
      tn := r.lm, td := 10 ^ r.ldp, htE := sfracEq r.lm r.ldp, tE := leftE }
  let siteR : BSN.HardyZSite :=
    { x := mkApp (mkConst ``ZIntervalEM.sndVal) I, M := r.rb, N := r.rco,
      tn := r.rm, td := 10 ^ r.rdp, htE := sfracEq r.rm r.rdp, tE := rightE }
  let signChange ← BSN.hardySignChangeSites siteL siteR (some D)
  let leftErr ← BSN.hardyErrOkFullSite siteL (some D)
  let rightErr ← BSN.hardyErrOkFullSite siteR (some D)
  return mkAppN (mkConst ``ZIntervalEM.Certificate.mk)
    #[I, leftNonneg, posPf r.lb, posPf r.lco, posPf r.rb, posPf r.rco,
      signChange, leftErr, rightErr]

/-- How many times `buildCertifiedEM` multiplies a failing row's working precision by
`precisionStepEM` before giving up, unless `build.sh --retries k` asks for more (`retriesEM`). -/
meta def precisionRetriesEM : Nat := 3

/-- The retries for this build: `ZETA_RS_RETRIES` (set by `build.sh --retries k`), else
`precisionRetriesEM`. Lake never caches a failed batch, so the value need not be in any trace. -/
meta def retriesEM : IO Nat :=
  return ((← IO.getEnv "ZETA_RS_RETRIES").bind String.toNat?).getD precisionRetriesEM

/-- The factor a failing row's working precision is raised by on each retry. -/
meta def precisionStepEM : Nat := 100

/-- `attempt D`, retried at `step · D`, `step² · D`, … up to `retries` more times while it throws;
the last failure is reported. -/
meta def withPrecisionRetries (label : String) (step D retries : Nat)
    (attempt : Nat → MetaM Expr) : MetaM Expr := do
  try attempt D
  catch err =>
    let mut err := err
    let mut D := D
    for _ in [0:retries] do
      D := D * step
      try return ← BSN.withPhase s!"{label}: raise precision to {D}" (attempt D)
      catch e => err := e
    throw err

/-- One row's `Certificate` proof, retrying the row alone at `precisionStepEM · D` up to `retries`
times if it does not build at `D`; the last failure is reported. -/
meta def buildCertifiedEM (r : Row) (D : Nat) (retries : Nat) : MetaM Expr :=
  withPrecisionRetries "EM" precisionStepEM D retries (buildCert r)

/-- The element type of the list `ofCertifiedEM` consumes, named so the metaprogram can cite it
as a constant. -/
abbrev CertPair := Σ' I : ZIntervalEM, I.Certificate

/-- The bundle's disjointness relation, named so the chain proof can be built by constant
application. Touching brackets are allowed: a shared endpoint has a certified nonzero `Z`. -/
def chainRel (I J : NonemptyInterval ℝ) : Prop := I.snd ≤ J.fst

private meta def certPairE : Expr := mkConst ``CertPair

/-- `⟨I, cert⟩ : CertPair`, with the family `β := ZIntervalEM.Certificate` explicit (`mkAppM`
would infer the constant family `fun _ ↦ I.Certificate`). -/
meta def mkCertPair (I cert : Expr) : Expr :=
  mkAppN (Expr.const ``PSigma.mk [Level.succ Level.zero, Level.zero])
    #[mkConst ``ZIntervalEM, mkConst ``ZIntervalEM.Certificate, I, cert]

private meta def chainRelE : Expr := mkConst ``chainRel
private meta def neiE : Expr := mkConst ``NEInterval

/-- The literal list `[elem xs[i], …, elem xs[xs.size - 1]] : List ty`, its elements built left to
right. -/
meta partial def buildListFrom {α : Type} (ty : Expr) (xs : Array α) (elem : α → MetaM Expr)
    (i : Nat) : MetaM Expr := do
  if h : i < xs.size then
    let x ← elem xs[i]
    return mkApp3 (Expr.const ``List.cons [Level.zero]) ty x (← buildListFrom ty xs elem (i + 1))
  else
    return mkApp (Expr.const ``List.nil [Level.zero]) ty

/-- Proof of `[nei rows[0], …].IsChain chainRel`, built right to left, with `lePf a b` the
`dec_le_dec` proof between adjacent rows `a`, `b`. -/
meta def buildChain {α : Type} (rows : Array α) (nei : α → MetaM Expr)
    (lePf : α → α → MetaM Expr) : MetaM Expr := do
  let neiT := neiE
  let neis ← rows.mapM nei
  let n := neis.size
  if n == 0 then return mkAppN (Expr.const ``List.IsChain.nil [Level.zero]) #[neiT, chainRelE]
  let mut tl := mkApp (Expr.const ``List.nil [Level.zero]) neiT
  let mut pf := mkAppN (Expr.const ``List.IsChain.singleton [Level.zero])
    #[neiT, chainRelE, neis[n - 1]!]
  for j in [0:n - 1] do
    let i := n - 2 - j
    if h : i + 1 < rows.size then
      let le ← lePf rows[i] rows[i + 1]
      pf := mkAppN (Expr.const ``List.IsChain.cons_cons [Level.zero])
        #[neiT, chainRelE, neis[i]!, neis[i + 1]!, tl, le, pf]
      tl := mkApp3 (Expr.const ``List.cons [Level.zero]) neiT neis[i + 1]! tl
  return pf

/-- The whole `CertifiedZeroIntervals` bundle for the rows, at one working precision per chunk
(the max of `rowPrecision`) so its rows hit the same `D`-keyed enclosure caches. -/
meta def buildBundle (rows : Array Row) (retries : Nat := precisionRetriesEM) : MetaM Expr := do
  let chunkD := rows.foldl (fun acc r ↦ max acc (rowPrecision r.lm r.ldp r.rm r.rdp)) 1
  let pairs ← buildListFrom certPairE rows (fun r ↦ do
    return mkCertPair (← buildInterval r) (← buildCertifiedEM r chunkD retries)) 0
  let disj ← buildChain rows buildNonemptyInterval fun a b ↦ decLeDec a.rm a.rdp b.lm b.ldp
  return mkAppN (mkConst ``CertifiedZeroIntervals.ofCertifiedEM) #[pairs, disj]

/-- The Euler–Maclaurin zero store `gen_zero_certificates.py` reads from, its rows in the same
`idx, fst, snd, fstCutoff, sndCutoff, fstBernoulli, sndBernoulli` layout `parseRows` expects. -/
meta def storeDir : System.FilePath := "python/out/euler_maclaurin/zeros"

open Elab Tactic in
/-- `build_certs lo hi` closes a `CertifiedZeroIntervals` goal with the bundle built from rows
`[lo, hi)` of the data file. -/
elab "build_certs " lo:num hi:num : tactic => do
  let e ← buildBundle (parseRows (← storeLines storeDir lo.getNat hi.getNat)) (← retriesEM)
  liftMetaFinishingTactic (·.assign e)

/-- Close a `BatchSpec n an ad bn bd` goal with `bundle`, the count and both endpoints each by
`Eq.refl`, which the kernel checks by reducing the bundle (so a drift between the generator's
statement and the rows cannot pass silently). -/
meta def closeBatchSpec (bundle : Expr) (goal : MVarId) : MetaM Unit := do
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let some (α, p) := ty.app2? ``Exists
    | throwError "build_batch: expected a `BatchSpec` goal, got{indentExpr ty}"
  let body := p.beta #[bundle]
  let some (h₁, rest) := body.and?
      | throwError "build_batch: malformed `BatchSpec`{indentExpr body}"
  let some (h₂, h₃) := rest.and? | throwError "build_batch: malformed `BatchSpec`{indentExpr body}"
  let rhs (h : Expr) : MetaM (Expr × Expr) := do
    let some (ty, _, r) := h.eq? | throwError "build_batch: malformed `BatchSpec`{indentExpr h}"
    return (ty, r)
  let refl (h : Expr) : MetaM Expr := do
    let (ty, r) ← rhs h
    return mkApp2 (mkConst ``Eq.refl [Level.one]) ty r
  let pf := mkApp4 (mkConst ``And.intro) h₁ rest (← refl h₁)
    (mkApp4 (mkConst ``And.intro) h₂ h₃ (← refl h₂) (← refl h₃))
  goal.assign (mkApp4 (mkConst ``Exists.intro [Level.one]) α p bundle pf)

open Elab Tactic in
/-- `build_batch lo hi` closes a `BatchSpec` goal from rows `[lo, hi)` of the Euler–Maclaurin
store. A failing row's working precision is raised up to `retriesEM` times. -/
elab "build_batch " lo:num hi:num : tactic => do
  let e ← buildBundle (parseRows (← storeLines storeDir lo.getNat hi.getNat)) (← retriesEM)
  liftMetaFinishingTactic (closeBatchSpec e)

end Zeta.Certificates
