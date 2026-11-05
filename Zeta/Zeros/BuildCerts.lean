module

public import Zeta.Zeros.Certificates.Basic
public import Zeta.Certificate.Named
public import Enclosure.BinarySplit.Tactic.Recognizer
public meta import Zeta.Certificate.Named

/-!
# Build the Euler–Maclaurin zero certificates directly from the data file

`build_certs lo hi` reads rows `[lo, hi)` of the zero store and emits a whole
`CertifiedZeroIntervals` as one `Expr` — the intervals, their `ZIntervalEM.Certificate`s and
the disjointness chain — with no generated named declarations in between. A batch module is
then a single line, and the bracket numbers live only in the data file.

The heavy fields (`is_sign_change`, `fst_error`, `snd_error`) are delegated to the `Enclosure`
cores in `Zeta.Certificate.Named`; everything else is a reflection proof over ℕ literals
(`dec_le_dec`, `dec_nonneg`, `pos_of_ble`), so the kernel only ever checks `Nat.ble`/`blt`.

The bundle is assembled through `CertifiedZeroIntervals.ofCertifiedEM`, the method-aware smart
constructor in `Certificates/Basic.lean`: it takes the `⟨interval, certificate⟩` pairs plus the
chain and derives `fst_nonneg`/`has_zero` itself, so this module never has to build the
existence proof. Batch-to-batch seams are `Basic.lean`'s `separated_of_le` against the
generator-emitted boundary abbrevs, and the assembled length comes from `join_length`; none of
that lives here any more.

Endpoints are imported exactly as the store writes them (`parseDec`). The search places each
boundary at the fewest decimal places that separate its two zeros (3, more only for a close pair;
`IMPORT_DP` in `python/src/config.py`), so the store already carries the precision Lean needs and
there is no import precision to keep in step with Python. `build_certs` re-verifies the sign
change and the error margin at whatever endpoints it builds.
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

/-- Rows `[lo, hi)` of the zero store in directory `store`, one line each. The store is split into
files (to stay under GitHub's file-size limit) that need not line up with the batches, so the
files are located through `manifest.json`, which lists them in order with their row counts; only
the files overlapping `[lo, hi)` are read. A file whose line count disagrees with the manifest, or
a range running past the store's end, is an error. -/
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

/-- Parse store lines into `Row`s. Each data row is
`idx, left, right, lco, rco, lb, rb` (7 columns); the leading index is dropped. A data
row is any line whose first character is a digit, so free-form header lines and the
`----` rule are skipped; any line that isn't exactly 7 columns is rejected. -/
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

/-- The decimal endpoint `m·10⁻ᵈᵖ` carried directly as `sfrac false m (10^dp)` (a raw ℕ ratio),
NOT as `OfScientific.ofScientific`: this keeps the kernel from ever reducing the decimal through
`Rat.ofScientific`/`Rat.mul`/… (which drag `HMul` over ℕ/ℤ into the check). -/
meta def ofSciReal (m dp : Nat) : MetaM Expr := do
  return mkApp3 (mkConst ``Enclosure.sfrac) (mkConst ``Bool.false) (mkNatLit m) (mkNatLit (10 ^ dp))

/-- The endpoint is already `sfrac false m (10^dp)`, so its `= sfrac …` fact is reflexivity. -/
meta def sfracEq (m dp : Nat) : Expr :=
  mkApp2 (mkConst ``Eq.refl [Level.one]) realTy
    (mkApp3 (mkConst ``Enclosure.sfrac) (mkConst ``Bool.false) (mkNatLit m) (mkNatLit (10 ^ dp)))

/-- The bundle's element type. Named so the metaprogram can cite it as a single constant:
`NonemptyInterval` takes an `[LE ℝ]` instance argument, and reconstructing that as an `Expr`
yields `[LE ℝ] → Type` rather than a `Type` unless the instance is synthesised explicitly. -/
abbrev NEInterval := NonemptyInterval ℝ

/-- One bracket as a `NEInterval`, with every argument explicit. The metaprogram applies this
rather than `NonemptyInterval.mk`, so it never has to produce the `LE ℝ` instance itself. -/
def mkNEI (a b : ℝ) (h : a ≤ b) : NEInterval := ⟨(a, b), h⟩

/-- One bracket plus its Euler–Maclaurin parameters, again fully explicit; see `mkNEI`. -/
def mkZI (a b : ℝ) (h : a ≤ b) (fc sc fb sb : ℕ) : ZIntervalEM :=
  ⟨mkNEI a b h, fc, sc, fb, sb⟩

/-- The `fst_le_snd` reflection proof for one row's endpoints. -/
meta def buildLeSnd (r : Row) : MetaM Expr := do
  let leftE ← ofSciReal r.lm r.ldp
  let rightE ← ofSciReal r.rm r.rdp
  return mkAppN (mkConst ``Enclosure.dec_le_dec)
    #[leftE, rightE, mkNatLit r.lm, mkNatLit (10 ^ r.ldp), mkNatLit r.rm, mkNatLit (10 ^ r.rdp),
      sfracEq r.lm r.ldp, sfracEq r.rm r.rdp, BSN.reflBoolTrue, BSN.reflBoolTrue, BSN.reflBoolTrue]

/-- The bare `NonemptyInterval ℝ` for one row: the endpoint pair plus `fst_le_snd`. This is what
the bundle actually stores — `ZIntervalEM`'s cutoff/Bernoulli parameters exist only to state the
certificate. -/
meta def buildNonemptyInterval (r : Row) : MetaM Expr := do
  return mkAppN (mkConst ``mkNEI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← buildLeSnd r]

/-- Build the `ZIntervalEM` term for one row: the `NonemptyInterval` it extends, then the four
Euler–Maclaurin parameters in field order (`fstCutoff`, `sndCutoff`, `fstBernoulli`,
`sndBernoulli`). -/
meta def buildInterval (r : Row) : MetaM Expr := do
  return mkAppN (mkConst ``mkZI)
    #[← ofSciReal r.lm r.ldp, ← ofSciReal r.rm r.rdp, ← buildLeSnd r,
      mkNatLit r.lco, mkNatLit r.rco, mkNatLit r.lb, mkNatLit r.rb]

/-- Working precision a single row's bracket needs: `base / width`, floored, where
`base = 1e5·max(1,t/30)` is the flat value that certifies at width ~1; wider brackets need less
precision, narrower ones more.
Width is `(rm·10^ldp − lm·10^rdp)/10^(ldp+rdp)`, so `D = base·10^(ldp+rdp)/wnum`. (#146)
The floor is `10000·t30²` (quadratic, not linear): the precision needed to keep `|Z|`'s magnitude
enclosure off zero grows faster than linearly in height, so a linear floor under-provisions wide
high-t brackets (they straddle zero); `t30²` gives ~1e4 at low t (unchanged) but ~2e7 at t≈1400. -/
meta def drow0 (r : Row) : Nat :=
  let t30 := max 1 (r.lm / (30 * 10 ^ r.ldp))
  let wnum := max 1 (r.rm * 10 ^ r.ldp - r.lm * 10 ^ r.rdp)
  max (10000 * t30 * t30) (100000 * t30 * 10 ^ (r.ldp + r.rdp) / wnum)

/-- Build the `Certificate` proof term for one row at working precision `D` (chosen once per
chunk by `buildBundle`, so every row shares the `D`-keyed enclosure caches): the mechanical
reflection fields, plus the three heavy fields (`is_sign_change`, `fst_error`, `snd_error`)
delegated to the hardy cores. -/
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

/-- The element type of the list `ofCertifiedEM` consumes, named so the metaprogram can cite it
as a constant rather than rebuilding the `PSigma` binder. -/
abbrev CertPair := Σ' I : ZIntervalEM, I.Certificate

/-- The bundle's disjointness relation. Definitionally the lambda `ofCertifiedEM` asks for; named
so the chain proof can be built by constant application. Touching brackets are allowed (`≤`, not
`<`): a shared endpoint has a certified nonzero `Z`, so the bracketed zeros stay distinct. -/
def chainRel (I J : NonemptyInterval ℝ) : Prop := I.snd ≤ J.fst

private meta def certPairE : Expr := mkConst ``CertPair

/-- `⟨I, cert⟩ : CertPair`, built with the dependent second component `β := ZIntervalEM.Certificate`
supplied explicitly. `mkAppM` cannot be used here: it would infer the *constant* family
`fun _ ↦ I.Certificate` from the type of `cert`, which is not the `Σ' I, I.Certificate` the bundle
is indexed by. -/
meta def mkCertPair (I cert : Expr) : Expr :=
  mkAppN (Expr.const ``PSigma.mk [Level.succ Level.zero, Level.zero])
    #[mkConst ``ZIntervalEM, mkConst ``ZIntervalEM.Certificate, I, cert]

private meta def chainRelE : Expr := mkConst ``chainRel
private meta def neiE : Expr := mkConst ``NEInterval

/-- `[⟨intervalᵢ, certᵢ⟩, …] : List CertPair` for rows `i…` as a literal cons `Expr`. This is the
list `ofCertifiedEM` takes; the certificates ride along inside it, so there is no separate
`∀ I ∈ …, I.Certificate` field to build. -/
meta partial def buildPairsFrom (rows : Array Row) (i : Nat) (D : Nat) : MetaM Expr := do
  if h : i < rows.size then
    let pair := mkCertPair (← buildInterval rows[i]) (← buildCert rows[i] D)
    return mkApp3 (Expr.const ``List.cons [Level.zero]) certPairE pair
      (← buildPairsFrom rows (i + 1) D)
  else
    return mkApp (Expr.const ``List.nil [Level.zero]) certPairE

/-- `[intervalᵢ.toNonemptyInterval, …]` for rows `i…`: the list the chain proof is stated about.
Definitionally the `l.map (·.1.toNonemptyInterval)` in `ofCertifiedEM`'s hypothesis, since
`List.map` on a literal cons unfolds. -/
meta partial def buildNeIntervalsFrom (rows : Array Row) (i : Nat) : MetaM Expr := do
  let nei := neiE
  if h : i < rows.size then
    return mkApp3 (Expr.const ``List.cons [Level.zero]) nei
      (← buildNonemptyInterval rows[i]) (← buildNeIntervalsFrom rows (i + 1))
  else
    return mkApp (Expr.const ``List.nil [Level.zero]) nei

/-- `dec_le_dec` proof that `ofSci(am,adp) ≤ ofSci(bm,bdp)`. -/
meta def decLeDec (am adp bm bdp : Nat) : MetaM Expr := do
  let aE ← ofSciReal am adp
  let bE ← ofSciReal bm bdp
  return mkAppN (mkConst ``Enclosure.dec_le_dec)
    #[aE, bE, mkNatLit am, mkNatLit (10 ^ adp), mkNatLit bm, mkNatLit (10 ^ bdp),
      sfracEq am adp, sfracEq bm bdp, BSN.reflBoolTrue, BSN.reflBoolTrue, BSN.reflBoolTrue]

/-- Proof of `[intervalᵢ.toNonemptyInterval, …].IsChain chainRel` via nested
`List.IsChain.cons_cons`, one `dec_le_dec` per adjacent pair. -/
meta partial def buildDisjFrom (rows : Array Row) (i : Nat) : MetaM Expr := do
  let nei := neiE
  if _ : i + 1 < rows.size then
    let lePf ← decLeDec rows[i].rm rows[i].rdp rows[i+1].lm rows[i+1].ldp
    return mkAppN (Expr.const ``List.IsChain.cons_cons [Level.zero])
      #[nei, chainRelE, ← buildNonemptyInterval rows[i], ← buildNonemptyInterval rows[i+1],
        ← buildNeIntervalsFrom rows (i + 2), lePf, ← buildDisjFrom rows (i + 1)]
  else if _ : i < rows.size then
    return mkAppN (Expr.const ``List.IsChain.singleton [Level.zero])
      #[nei, chainRelE, ← buildNonemptyInterval rows[i]]
  else
    return mkAppN (Expr.const ``List.IsChain.nil [Level.zero]) #[nei, chainRelE]

/-- Build the whole `CertifiedZeroIntervals` bundle (intervals + certs + disj) from the rows.
Working precision is ONE value per chunk: the max over its rows of `drow0`. Every row then gets at
least the precision its own bracket width needs (so all margins pass), while a single `D` keeps the
`D`-keyed enclosure caches (`piVal`/`log`/`√`/`trigReduce`) shared across the chunk — cache
sharing dominates the per-row precision saving, and this is the LOWEST `D` that preserves that
sharing. (#146) -/
meta def buildBundle (rows : Array Row) : MetaM Expr := do
  let chunkD := rows.foldl (fun acc r => max acc (drow0 r)) 1
  return mkAppN (mkConst ``CertifiedZeroIntervals.ofCertifiedEM)
    #[← buildPairsFrom rows 0 chunkD, ← buildDisjFrom rows 0]

/-- The Euler–Maclaurin zero store `gen_zero_certificates.py` reads from, its rows in the same
`idx, fst, snd, fstCutoff, sndCutoff, fstBernoulli, sndBernoulli` layout `parseRows` expects. -/
meta def storeDir : System.FilePath := "python/out/euler_maclaurin/zeros"

open Elab Tactic in
/-- `build_certs lo hi` closes a `CertifiedZeroIntervals` goal by building the bundle directly
from rows `[lo, hi)` of the data file — no named declarations, no `fin_cases`. -/
elab "build_certs " lo:num hi:num : tactic => do
  let e ← buildBundle (parseRows (← storeLines storeDir lo.getNat hi.getNat))
  liftMetaFinishingTactic (·.assign e)

/-- Close a `BatchSpec n an ad bn bd` goal with the bundle `bundle`: `Exists.intro` on the
bundle, and the three conjuncts — count, first endpoint, last endpoint — each by `Eq.refl` of
the goal's own right-hand side. The kernel checks them by reducing the bundle (a `List.length`
and two list projections), so the batch module needs no per-batch lemmas at all: the statement
carries what the assembler consumes, and this term is its whole proof.

The statement is written by the generator from the same rows, parsed the same way; if the
two disagree the kernel rejects the `Eq.refl`, so a rounding drift between Python and Lean cannot
pass silently. -/
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
store: the bundle by `buildBundle`, the statement's three facts by `closeBatchSpec`. -/
elab "build_batch " lo:num hi:num : tactic => do
  let e ← buildBundle (parseRows (← storeLines storeDir lo.getNat hi.getNat))
  liftMetaFinishingTactic (closeBatchSpec e)

end Zeta.Certificates
