module

public import Native.Batch
public import Zeta.Zeros.BuildCertsRS
-- `native_decide` evaluates `checkTiling` at compile time, in every module using the tactic
public meta import Native.Eval.Batch
public meta import Native.Eval.Store

/-!
# `build_batch_rs +native`: a Riemann–Siegel batch checked by compiled evaluation

`build_batch_rs +native lo hi` closes the same `BatchSpec` goal as `build_batch_rs lo hi`, from the
same store rows `[lo, hi)` read and parsed by the same `parseRowsRS`, but by
`batchSpec_of_tiling … (by native_decide)` instead of a kernel-checked certificate: the brackets
run between consecutive boundaries (every left endpoint, then the last right one), and
`Native.checkTiling` re-certifies each of them. The resulting theorem trusts the Lean compiler.

It lives on the `Native` side, so the kernel proof's import closure never contains the native
checker.
-/
@[expose] public section

open Lean Elab Tactic Meta

-- this tactic is where the `Native` trust level uses `native_decide`, by design
set_option linter.style.nativeDecide false

namespace Native

/-- `checkTiling`'s working precision for the linear-free approximant. -/
meta def nativePrec : Nat := 2 ^ 64

/-- `checkTiling`'s working precision for the full approximant (the fallback near close pairs). -/
meta def nativeFallbackPrec : Nat := 2 ^ 128

/-- Parse `lines`, the store's rows from `lo` on, as rows `[lo, hi)`: parsed exactly as
`parseRowsRS` parses them, and each checked against its index column. -/
meta def parseSliceRS (lines : List String) (lo hi : Nat) :
    Except String (Array Zeta.Certificates.RowRS) :=
  go (lines.take (hi - lo)) lo #[]
where
  /-- From row `k` on. -/
  go : List String → Nat → Array Zeta.Certificates.RowRS →
      Except String (Array Zeta.Certificates.RowRS)
    | [], k, rows =>
      if rows.size == hi - lo then .ok rows
      else .error s!"store has {k} rows; batch wants [{lo}, {hi})"
    | line :: rest, k, rows => do
      let [idx, l, r] := (line.replace " " "").splitOn ","
        | .error s!"store row {k + 1}: expected 3 columns, got `{line}`"
      unless idx.toNat? == some (k + 1) do
        .error s!"store row {k + 1}: index column reads `{idx}`"
      let (lm, ldp) := Zeta.Certificates.parseDec l
      let (rm, rdp) := Zeta.Certificates.parseDec r
      go rest (k + 1) (rows.push { lm, ldp, rm, rdp })

/-- The store file last read by this process, with its `lineStarts`: a module's batches mostly
read the same file, so it is read and indexed once. -/
meta initialize storeCache : IO.Ref (Option (System.FilePath × ByteArray × Array USize)) ←
  IO.mkRef none

/-- The store file at `path` and its line starts, from `storeCache` if it holds that file. -/
meta def readStoreFile (path : System.FilePath) : IO (ByteArray × Array USize) := do
  if let some (p, b, starts) := ← storeCache.get then
    if p == path then return (b, starts)
  let b ← IO.FS.readBinFile path
  let starts := lineStarts b
  storeCache.set (some (path, b, starts))
  return (b, starts)

/-- Rows `[lo, hi)` of the zero store in directory `store`, as `parseRowsRS` gives them. The files
overlapping `[lo, hi)` are located through `manifest.json`, as in `storeLines`, and of each only
those rows' bytes are decoded rather than the whole file split. -/
meta def readRowsRS (store : System.FilePath) (lo hi : Nat) :
    IO (Except String (Array Zeta.Certificates.RowRS)) := do
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile (store / "manifest.json"))
  let files ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "files"
  let mut text := ""
  let mut start := 0
  for f in files do
    let n ← IO.ofExcept <| f.getObjValAs? Nat "rows"
    if lo < start + n && start < hi then
      let (b, starts) ← readStoreFile (store / (← IO.ofExcept <| f.getObjValAs? String "file"))
      text := text ++ linesBetween b starts (lo - start) (min hi (start + n) - start)
    start := start + n
  return parseSliceRS (text.splitOn "\n") lo hi

/-- The batch's boundaries as `(numerator, denominator)`: every left endpoint, then the last right
one. -/
meta def boundariesRS (rows : Array Zeta.Certificates.RowRS) : Array (Nat × Nat) :=
  rows.map (fun r => (r.lm, 10 ^ r.ldp)) ++
    (rows.back?.map fun r => #[(r.rm, 10 ^ r.rdp)]).getD #[]

/-! ### Diagnosing a failed batch

When `native_decide` reports `false`, the batch is re-evaluated bracket by bracket (with the same
compiled code) to say which zeros failed and why. This runs only on failure and proves nothing. -/

/-- `x` for display: fixed point for moderate magnitudes, scientific otherwise. -/
meta def fmt (x : Float) : String :=
  if x == 0 then "0"
  else
    let e := (Float.log10 x.abs).floor
    if -3 ≤ e && e < 7 then toString x
    else s!"{toString ((x / Float.pow 10 e * 10000).round / 10000)}e{e.toInt64}"

/-- `n/d` for display. -/
meta def fmtRat (n d : Nat) : String := fmt (n.toFloat / d.toFloat)

/-- An enclosure `±c ± r` for display. -/
meta def fmtEncl (e : Encl) : String :=
  s!"{if e.neg then "-" else ""}{fmtRat e.cn e.cd} ± {fmtRat e.rn e.rd}"

/-- What the linear-free check sees at the endpoint `t`, against the batch's error bound `B`. -/
meta def endpointReport (tab : TermTable) (t : Nat × Nat) (W : Nat) (B : Option Encl) : String :=
  match approx₀F tab t.1 t.2 W, B with
  | none, _ => s!"at t = {fmtRat t.1 t.2}, Z̃ was not evaluated (an enclosure step failed at this \
      working precision, or t is too close to a change of cutoff 2πk²)"
  | some Z, none =>
    s!"at t = {fmtRat t.1 t.2}, Z̃ = {fmtEncl Z} but the error bound was not evaluated"
  | some Z, some E =>
    match certifiedSign (some Z) (some E) with
    | some sg =>
      s!"at t = {fmtRat t.1 t.2}, Z̃ = {fmtEncl Z}: {if sg then "negative" else "positive"}"
    | none => s!"at t = {fmtRat t.1 t.2}, Z̃ = {fmtEncl Z} is not certified: |Z̃| must exceed the \
        error bound {fmtEncl E} with the enclosure excluding 0"

/-- Why the bracket from `a` to `b` fails, or `none` if it passes. -/
meta def bracketReport (tab : TermTable) (a b : Nat × Nat) (W W₁ : Nat) (B : Option Encl) :
    Option String :=
  if !rowOk ⟨a.1, a.2, b.1, b.2⟩ then
    some s!"[{fmtRat a.1 a.2}, {fmtRat b.1 b.2}] is out of order or below 32π"
  else if signsDiffer (endpointSign₀ tab a.1 a.2 W B) (endpointSign₀ tab b.1 b.2 W B) ||
      fallbackOk a b W₁ then none
  else
    some s!"no certified sign change on [{fmtRat a.1 a.2}, {fmtRat b.1 b.2}], nor under the full \
      approximant (C₁ fallback):\n      {endpointReport tab a W B}\n      \
      {endpointReport tab b W B}"

/-- At most this many failing zeros are listed. -/
meta def maxReported : Nat := 20

/-- Every failure of the batch with boundaries `bs` from store row `lo` against the statement
`BatchSpec n an ad bn bd`: the statement's count and ends, then each failing bracket by its zero's
store index. -/
meta def diagnoseTiling (bs : Array (Nat × Nat)) (lo : Nat) (W W₁ n an ad bn bd : Nat) :
    Array String := Id.run do
  let mut out : Array String := #[]
  if bs.size < 2 then return #["the batch has no brackets"]
  if bs.size - 1 != n then
    out := out.push s!"the statement has {n} brackets, the store rows give {bs.size - 1}"
  if bs[0]! != (an, ad) then
    out := out.push s!"the statement starts at {an}/{ad}, the store at {bs[0]!.1}/{bs[0]!.2}"
  if bs.back! != (bn, bd) then
    out := out.push s!"the statement ends at {bn}/{bd}, the store at {bs.back!.1}/{bs.back!.2}"
  let tab := termTable ((cutoff bs.back!.1 bs.back!.2).getD 0) W
  let B := errBound bs[0]!.1 bs[0]!.2 W
  let mut failed := 0
  for i in [0:bs.size - 1] do
    if let some why := bracketReport tab bs[i]! bs[i + 1]! W W₁ B then
      failed := failed + 1
      if failed ≤ maxReported then
        out := out.push s!"zero #{lo + i + 1}: {why}"
  if failed > maxReported then
    out := out.push s!"… and {failed - maxReported} more failing zeros"
  return out

/-! ### Will the kernel-checked build pass this batch?

The kernel metaprogram (`build_batch_rs`) certifies the same values, but with enclosures much
wider than these: at the batch's working precision `D` (`batchPrecRS`), raised
`precisionStepRS`-fold up to `precisionRetriesRS` times (or `build.sh --retries k`) when a row
fails. Measured against its
exact fields (all of 1e4, 31 batches across 1e6, the top of 1e7), its enclosure of `Z̃` is at most
`0.79·kernelWidth`, and of the error bound at most `3.3/D`. A margin by which `|Z̃|` clears the
error bound here, at least twice those widths, therefore clears in the kernel too. Each zero
whose margin needs a raise is reported with how many; `build.sh` compares that against the
kernel's retries and warns of the zeros they do not cover. This only reports; it proves nothing. -/

/-- The marker of a line reporting a zero the kernel-checked build needs to retry (or cannot
certify); `build.sh --native` collects every line carrying it. -/
meta def kernelRiskMarker : String := "KERNEL PRECISION"

/-- An upper bound on the kernel's enclosure width of `Z̃` at `t` with cutoff `ν`, precision `D`:
`(6·√ν·t + 50/|cos 2πp|)/D` with `p = √(t/2π) − ν` (the main sum's errors grow with `√ν·t`; the
zero-order correction divides by `cos 2πp`). -/
meta def kernelWidth (t : Float) (ν : Nat) (D : Float) : Float :=
  let pi := 3.141592653589793
  let p := Float.sqrt (t / (2 * pi)) - ν.toFloat
  (6 * Float.sqrt ν.toFloat * t + 50 / (Float.cos (2 * pi * p)).abs) / D

/-- The kernel's enclosure width of the error bound at precision `D`. -/
meta def kernelErrWidth (D : Float) : Float := 4 / D

/-- `|Z| − E`: by how much the enclosure `Z` clears the upper end of the enclosure `E` (negative if
it does not). -/
meta def margin (Z E : Encl) : Float :=
  let v (neg : Bool) (n d : Nat) : Float :=
    if neg then -(n.toFloat / d.toFloat) else n.toFloat / d.toFloat
  (v false Z.cn Z.cd - v false Z.rn Z.rd) - (v E.neg E.cn E.cd + v false E.rn E.rd)

/-- How many `precisionStepRS`-fold raises of `D` the kernel needs at `t` to clear `margin` with the
widths doubled, if at most `limit`. -/
meta def retriesNeeded (t : Nat × Nat) (D : Nat) (m : Float) (limit : Nat) : Option Nat := do
  let ν ← BSN.cutoffRS? t.1 t.2
  let tf := t.1.toFloat / t.2.toFloat
  (List.range (limit + 1)).find? fun k =>
    let Dk := D.toFloat * (Zeta.Certificates.precisionStepRS.toFloat ^ k.toFloat)
    m > 2 * (kernelWidth tf ν Dk + kernelErrWidth Dk)

/-- The most raises `kernelRisks` looks for: beyond `precisionStepRS^20` the margin is as good as
none, and only moving the endpoint helps. -/
meta def maxRaises : Nat := 20

/-- The zeros of the batch with boundaries `bs` (store rows from `lo`) that the kernel-checked
build will not certify at the batch's precision `D`: each with how many raises of `D` it needs
(`needs k raise`), or why no number does (its full approximant refused, `c1ExtraBits` beyond 200
bits, or no margin left: `move this endpoint`). Each row is judged by the certificate this check
used for it: the linear-free one against the batch's error bound, or the full one against its
own. -/
meta def kernelRisks (bs : Array (Nat × Nat)) (lo D W W₁ : Nat) : Array String := Id.run do
  if bs.size < 2 then return #[]
  let tab := termTable ((cutoff bs.back!.1 bs.back!.2).getD 0) W
  let tab₁ := termTable 0 W₁
  let B := errBound bs[0]!.1 bs[0]!.2 W
  let mut out := #[]
  for i in [0:bs.size - 1] do
    let (a, b) := (bs[i]!, bs[i + 1]!)
    let linFree := signsDiffer (endpointSign₀ tab a.1 a.2 W B) (endpointSign₀ tab b.1 b.2 W B)
    for t in [a, b] do
      let m := if linFree then
          (approx₀F tab t.1 t.2 W).bind fun Z => B.map (margin Z)
        else (approx₁ tab₁ t.1 t.2 W₁).bind fun Z => (errBound₁ t.1 t.2 W₁).map (margin Z)
      let some m := m | continue
      let at_ := s!"zero #{lo + i + 1} at t = {fmtRat t.1 t.2}"
      if !linFree then
        if let some ν := BSN.cutoffRS? t.1 t.2 then
          let bits := BSN.c1ExtraBits t.1 t.2 ν
          if bits > 200 then
            out := out.push s!"{at_}: the kernel refuses the full approximant here (cos 2πp needs \
              {bits} > 200 extra bits); move this endpoint"
            continue
      match retriesNeeded t D m maxRaises with
      | some k =>
        if k > 0 then
          out := out.push s!"{at_}: |Z̃| clears the error bound by {fmt m}; the kernel needs {k} \
            raise{if k == 1 then "" else "s"} of the working precision"
      | none =>
        out := out.push s!"{at_}: |Z̃| clears the error bound by only {fmt m}; no number of \
          retries rescues it (beyond {maxRaises}): move this endpoint"
  return out

/-- The `Nat` literal arguments of a `BatchSpec n an ad bn bd` goal. -/
meta def batchSpecArgs (goal : Expr) : MetaM (Option (Array Nat)) := do
  let goal ← instantiateMVars goal
  unless goal.isAppOfArity ``Zeta.Certificates.BatchSpec 5 do return none
  let mut ns := #[]
  for a in goal.getAppArgs do
    let some k ← Meta.evalNat a | return none
    ns := ns.push k
  return some ns

/-- `build_batch_rs +native lo hi` closes a `BatchSpec` goal from rows `[lo, hi)` of the
Riemann–Siegel store by `native_decide` on `checkTiling`, and warns of rows the kernel-checked
`build_batch_rs` will need to retry (`kernelRisks`), which `build.sh --native` checks against the
kernel's retries. -/
elab "build_batch_rs " "+native " lo:num hi:num : tactic => do
  let rows ← match ← readRowsRS Zeta.Certificates.storeDirRS lo.getNat hi.getNat with
    | .ok rows => pure rows
    | .error msg => throwError msg
  let bs := boundariesRS rows
  let elems ← bs.mapM fun (n, d) => `(($(quote n), $(quote d)))
  let goal ← getMainTarget
  evalTactic (← `(tactic|
    refine batchSpec_of_tiling [$elems,*] $(quote nativePrec) $(quote nativeFallbackPrec)
      _ _ _ _ _ ?_))
  -- a separate step, so that its failure is thrown here rather than logged
  try evalTactic (← `(tactic| native_decide))
  catch err =>
    let some #[n, an, ad, bn, bd] ← batchSpecArgs goal | throw err
    let report := diagnoseTiling bs lo.getNat nativePrec nativeFallbackPrec n an ad bn bd
    if report.isEmpty then throw err
    throwError m!"build_batch_rs +native: store rows [{lo.getNat}, {hi.getNat}) do not \
      certify this batch:\n  " ++ "\n  ".intercalate report.toList
  let risks := kernelRisks bs lo.getNat (Zeta.Certificates.batchPrecRS rows) nativePrec
    nativeFallbackPrec
  unless risks.isEmpty do
    logInfo <| "\n".intercalate <| risks.toList.map fun r =>
      s!"{kernelRiskMarker}: store rows [{lo.getNat}, {hi.getNat}): {r}"

end Native
