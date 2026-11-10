/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Zeta.Certificate.Bernoulli
public import Zeta.Certificate.HardyZDefs
public import Zeta.Certificate.Cpow
public import Zeta.Certificate.HardyZ
public meta import Zeta.Certificate.HardyZ

/-!
# Named rectangle enclosures

Threads *named* values (`zetaApproximant …`, `(ascPochhammer ℂ m).eval s`, …) through the
rectangle arithmetic:

- a `CNamed` is a rectangle proof `Complex.IsNear z …` for an explicit `z`, with the components
  recovered as `And` projections;
- `cAddNamed`/`cSubNamed`/`cMulNamed` combine components through `Complex.IsNear.addLitP`,
  `subLitP` and `mul`, naming the result `z + w`/`z - w`/`z * w`;
- `cnamedOfEq` renames along a proven equality (a leaf or step identity).

Interval arithmetic carries all values; the equalities only ever rename.
-/
@[expose] public section


namespace BSN
open Enclosure

open Complex Complex.Stirling

open Lean Meta

/-- Trace class for the coarse phases of the certificate tactics (`hardy_sign_change`,
`hardy_error_ok_full`, `gram_bound`), attributing elaboration time to the enclosure builders. -/
initialize registerTraceClass `BSN.phases

/-- Wrap a builder phase in a `trace.BSN.phases` node for profiler attribution. -/
meta def withPhase {α : Type} (name : String) (k : MetaM α) : MetaM α :=
  withTraceNode `BSN.phases (fun _ ↦ return m!"{name}") k

/-- The LHS of the equality a renaming lemma proves, read from the lemma's declared type
instantiated at the arguments of `he = f a₀ … aₖ` (`f` a constant whose type ends in an `Eq`)
rather than by `inferType`. For surface forms (a `Finset.sum`, an
`⟨sfrac, sfrac⟩` rectangle, a mathlib projection) whose exact numeral shapes are hard to build by
hand; plain applications are built directly at the producer. -/
meta def lemmaLhs (he : Expr) : MetaM Expr := do
  let fn := he.getAppFn
  let some nm := fn.constName?
    | throwError "lemmaLhs: head is not a constant: {he}"
  let ty := (← getConstInfo nm).type
  let inst ← instantiateForall ty he.getAppArgs
  let_expr Eq _ l _ := inst
    | throwError "lemmaLhs: {nm}'s conclusion is not an `Eq`: {inst}"
  return l

/-- `ofEqNear` for the named layer: transport the enclosure along `he` onto its LHS `z'`, which
the caller passes directly rather than having it read back by `inferType`. -/
meta def ofEqNearHe (z' he : Expr) (r : RNear) : MetaM RNear := do
  ofEqNear z' he r

/-- A named rectangle: a kernel proof of `Complex.IsNear z …` for the explicit complex value
`z`, together with the component enclosures (the `And` projections of `proof`, enclosing
`z.re` and `z.im`). -/
structure CNamed where
  z : Expr
  proof : Expr
  re : RNear
  im : RNear

/-- Package a rectangle proof about `z` into a `CNamed`: the component proofs go through the
`Complex.IsNear.re_isNear`/`im_isNear` accessor lemmas. -/
meta def mkCNamed (z proof : Expr) (re im : RNear) : MetaM CNamed := do
  let args := #[z, toExpr re.neg, natLitShared re.cn, natLitShared re.cd, natLitShared re.rn,
    natLitShared re.rd, toExpr im.neg, natLitShared im.cn, natLitShared im.cd, natLitShared im.rn,
    natLitShared im.rd, proof]
  let reProof := mkAppN (mkConst ``Complex.IsNear.re_isNear) args
  let imProof := mkAppN (mkConst ``Complex.IsNear.im_isNear) args
  -- `re_isNear`/`im_isNear` conclude `Real.IsNear z.re …`/`Real.IsNear z.im …`, so the component
  -- reals are `Complex.re z`/`Complex.im z`, built directly.
  return { z, proof, re := { re with proof := reProof, x := mkApp (mkConst ``Complex.re) z },
                     im := { im with proof := imProof, x := mkApp (mkConst ``Complex.im) z } }

/-! The result complex value of a combinator is a fixed function of its inputs' values, built
directly to match the `Complex.IsNear.add/sub/mul/mk` conclusions; the kernel checks the match. -/

private meta def cplxTyE : Expr := mkConst ``Complex

/-- `z * w` on `ℂ`. -/
meta def mkMulC (z w : Expr) : Expr :=
  mkAppN (mkConst ``HMul.hMul [.zero, .zero, .zero])
    #[cplxTyE, cplxTyE, cplxTyE,
      mkApp2 (mkConst ``instHMul [.zero]) cplxTyE (mkConst ``Complex.instMul),
      z, w]

/-- `z + w` on `ℂ`. -/
meta def mkAddC (z w : Expr) : Expr :=
  mkAppN (mkConst ``HAdd.hAdd [.zero, .zero, .zero])
    #[cplxTyE, cplxTyE, cplxTyE,
      mkApp2 (mkConst ``instHAdd [.zero]) cplxTyE (mkConst ``Complex.instAdd),
      z, w]

/-- `z - w` on `ℂ`. -/
meta def mkSubC (z w : Expr) : Expr :=
  mkAppN (mkConst ``HSub.hSub [.zero, .zero, .zero])
    #[cplxTyE, cplxTyE, cplxTyE,
      mkApp2 (mkConst ``instHSub [.zero]) cplxTyE (mkConst ``Complex.instSub),
      z, w]

/-- `⟨re, im⟩ : ℂ` (`Complex.mk re im`), the value of a `Complex.IsNear.mk` leaf. -/
meta def mkMkC (re im : Expr) : Expr := mkApp2 (mkConst ``Complex.mk) re im

/-- A `CNamed` from componentwise projection enclosures (as `cLogNear` produces), through
`Complex.IsNear.of_parts`. -/
meta def cnamedOfParts (z : Expr) (c : CNear) : CNamed :=
  let proof := mkAppN (mkConst ``Complex.IsNear.of_parts)
    #[z, toExpr c.re.neg, natLitShared c.re.cn, natLitShared c.re.cd, natLitShared c.re.rn,
      natLitShared c.re.rd, toExpr c.im.neg, natLitShared c.im.cn, natLitShared c.im.cd,
      natLitShared c.im.rn, natLitShared c.im.rd, c.re.proof, c.im.proof]
  { z, proof, re := c.re, im := c.im }

/-- Checkpoint stride: seal the accumulated proof once every this many accumulation steps.
Higher stride means fewer, larger sealed lemmas (fewer `addDecl` calls, higher peak memory). -/
meta def checkpointStride : ℕ := 8

/-- Seal a named rectangle's accumulated proof behind a statement-keyed module aux lemma (like
`cachedNear`), so later accumulation steps cite the constant. -/
meta def cnamedCheckpoint (x : CNamed) : MetaM CNamed := do
  let ty := mkAppN (mkConst ``Complex.IsNear)
    #[x.z, toExpr x.re.neg, natLitShared x.re.cn, natLitShared x.re.cd, natLitShared x.re.rn,
      natLitShared x.re.rd, toExpr x.im.neg, natLitShared x.im.cn, natLitShared x.im.cd,
      natLitShared x.im.rn, natLitShared x.im.rd]
  let nm ← mkAuxLemma [] ty x.proof
  mkCNamed x.z (mkConst nm) x.re x.im

/-- Rename a named rectangle along `he : z' = z` (`Complex.IsNear.of_eq`). The caller passes the
target name `z'` (the equality's LHS) directly. -/
meta def cnamedOfEq (z' he : Expr) (x : CNamed) : MetaM CNamed := do
  let proof := mkAppN (mkConst ``Complex.IsNear.of_eq)
    #[z', x.z, toExpr x.re.neg, natLitShared x.re.cn, natLitShared x.re.cd, natLitShared x.re.rn,
      natLitShared x.re.rd, toExpr x.im.neg, natLitShared x.im.cn, natLitShared x.im.cd,
      natLitShared x.im.rn, natLitShared x.im.rd, he, x.proof]
  mkCNamed z' proof x.re x.im

/-- Exact constant leaf: the radius-zero rectangle named `Z`, given a leaf identity
`he : Z = ⟨sfrac rneg rcn rcd, sfrac ineg icn icd⟩`. -/
meta def cnamedConst (he : Expr) (rneg : Bool) (rcn rcd : ℕ) (ineg : Bool) (icn icd : ℕ) :
    MetaM CNamed := do
  let mkC (neg : Bool) (cn cd : ℕ) : MetaM RNear := do
    let proof :=
        mkAppN (mkConst ``Real.IsNear.const) #[toExpr neg, natLitShared cn, natLitShared cd]
    return { proof, x := mkSfracR neg cn cd, neg, cn, cd, rn := 0, rd := 1 }
  let reC ← mkC rneg rcn rcd
  let imC ← mkC ineg icn icd
  let pf := mkAppN (mkConst ``Complex.IsNear.mk)
    #[reC.x, imC.x, toExpr rneg, natLitShared rcn, natLitShared rcd,
      natLitShared 0, natLitShared 1, toExpr ineg, natLitShared icn, natLitShared icd,
      natLitShared 0, natLitShared 1, reC.proof, imC.proof]
  let zmk := mkMkC reC.x imC.x
  cnamedOfEq (← lemmaLhs he) he { z := zmk, proof := pf, re := reC, im := imC }

/-- Named product: the combined components `reS`/`imS` passed through the rectangle lemma `thm`
(`Complex.IsNear.mul`), named `x.z * y.z`. -/
private meta def cnamedCombine (thm : Name) (x y : CNamed) (reS imS : RNear) : MetaM CNamed := do
  let proof := mkAppN (mkConst thm)
    #[x.z, y.z, toExpr reS.neg, natLitShared reS.cn, natLitShared reS.cd, natLitShared reS.rn,
      natLitShared reS.rd, toExpr imS.neg, natLitShared imS.cn, natLitShared imS.cd,
      natLitShared imS.rn, natLitShared imS.rd, reS.proof, imS.proof]
  -- `cnamedCombine` is used only for `Complex.IsNear.mul`, whose conclusion is about `z * w`.
  let z' := mkMulC x.z y.z
  mkCNamed z' proof reS imS

/-- Named `add`/`sub` through one application of the paired-input lemma `thm`
(`Complex.IsNear.addLitP`/`subLitP`), recentring any component that exceeds the renorm cap. -/
private meta def cnamedCombineP (thm : Name) (x y : CNamed) (sub : Bool) : MetaM CNamed := do
  let (rNeg, rCnPre) := addCentreFields x.re y.re sub
  let (iNeg, iCnPre) := addCentreFields x.im y.im sub
  let (rCn, rCd, rRn, rRd) := addLikeFields x.re y.re rCnPre
  let (iCn, iCd, iRn, iRd) := addLikeFields x.im y.im iCnPre
  let proof := mkAppN (mkConst thm)
    #[x.z, y.z,
      toExpr x.re.neg, natLitShared x.re.cn, natLitShared x.re.cd, natLitShared x.re.rn,
      natLitShared x.re.rd, toExpr x.im.neg, natLitShared x.im.cn, natLitShared x.im.cd,
      natLitShared x.im.rn, natLitShared x.im.rd,
      toExpr y.re.neg, natLitShared y.re.cn, natLitShared y.re.cd, natLitShared y.re.rn,
      natLitShared y.re.rd, toExpr y.im.neg, natLitShared y.im.cn, natLitShared y.im.cd,
      natLitShared y.im.rn, natLitShared y.im.rd,
      toExpr rNeg, natLitShared rCnPre, natLitShared rCn, natLitShared rCd, natLitShared rRn,
      natLitShared rRd,
      toExpr iNeg, natLitShared iCnPre, natLitShared iCn, natLitShared iCd, natLitShared iRn,
      natLitShared iRd,
      x.proof, y.proof,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  let z' := if sub then mkSubC x.z y.z else mkAddC x.z y.z
  let reX := mkApp (mkConst ``Complex.re) z'
  let imX := mkApp (mkConst ``Complex.im) z'
  let mkR (xv : Expr) (neg : Bool) (f : ℕ × ℕ × ℕ × ℕ) : RNear :=
    { proof, x := xv, neg, cn := f.1, cd := f.2.1, rn := f.2.2.1, rd := f.2.2.2 }
  let base := #[z', toExpr rNeg, natLitShared rCn, natLitShared rCd, natLitShared rRn,
    natLitShared rRd, toExpr iNeg, natLitShared iCn, natLitShared iCd, natLitShared iRn,
    natLitShared iRd]
  match renormFields? rCn rCd rRn rRd, renormFields? iCn iCd iRn iRd with
  | none, none =>
    mkCNamed z' proof (mkR reX rNeg (rCn, rCd, rRn, rRd)) (mkR imX iNeg (iCn, iCd, iRn, iRd))
  | some (rCn', rCd', rRn', rRd'), none =>
    let proof := mkAppN (mkConst ``Complex.IsNear.recentreRe) (base ++
      #[natLitShared rCn', natLitShared rCd', natLitShared rRn', natLitShared rRd', proof,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue])
    mkCNamed z' proof (mkR reX rNeg (rCn', rCd', rRn', rRd')) (mkR imX iNeg (iCn, iCd, iRn, iRd))
  | none, some (iCn', iCd', iRn', iRd') =>
    let proof := mkAppN (mkConst ``Complex.IsNear.recentreIm) (base ++
      #[natLitShared iCn', natLitShared iCd', natLitShared iRn', natLitShared iRd', proof,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue])
    mkCNamed z' proof (mkR reX rNeg (rCn, rCd, rRn, rRd)) (mkR imX iNeg (iCn', iCd', iRn', iRd'))
  | some (rCn', rCd', rRn', rRd'), some (iCn', iCd', iRn', iRd') =>
    let proof := mkAppN (mkConst ``Complex.IsNear.recentre2) (base ++
      #[natLitShared rCn', natLitShared rCd', natLitShared rRn', natLitShared rRd',
        natLitShared iCn', natLitShared iCd', natLitShared iRn', natLitShared iRd',
        proof,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue])
    mkCNamed z' proof (mkR reX rNeg (rCn', rCd', rRn', rRd'))
      (mkR imX iNeg (iCn', iCd', iRn', iRd'))

/-- Named addition through the paired-input lemma (`Complex.IsNear.addLitP`); the result is
named `x.z + y.z`. -/
meta def cAddNamed (x y : CNamed) : MetaM CNamed := do
  cnamedCombineP ``Complex.IsNear.addLitP x y false

/-- Named subtraction (`Complex.IsNear.subLitP`). -/
meta def cSubNamed (x y : CNamed) : MetaM CNamed := do
  cnamedCombineP ``Complex.IsNear.subLitP x y true

/-- Named multiplication, componentwise through `Complex.IsNear.mul`. -/
meta def cMulNamed (x y : CNamed) : MetaM CNamed := do
  let reS ← subNear (← mulNearRaw x.re y.re) (← mulNearRaw x.im y.im)
  let imS ← addNear (← mulNearRaw x.re y.im) (← mulNearRaw x.im y.re)
  cnamedCombine ``Complex.IsNear.mul x y reS imS

/-! ### Named leaves at `s = ½ + i·t` -/

/-- The `Expr` of `sfrac neg n d`. -/
meta def sfracExpr (neg : Bool) (n d : ℕ) : Expr :=
  mkApp3 (mkConst ``sfrac) (toExpr neg) (natLitShared n) (natLitShared d)

/-- Named rectangle of `s = ½ + i·t` for `t` an opaque real with recogniser proof
`ht : t = sfrac tneg tn td`. -/
meta def mkSNamed (tE htE : Expr) (tneg : Bool) (tn td : ℕ) : MetaM CNamed := do
  let he := mkAppN (mkConst ``s_crit_mk) #[tE, toExpr tneg, natLitShared tn, natLitShared td, htE]
  cnamedConst he false 1 2 tneg tn td

/-- Named rectangle of `s + n` (`s = ½ + i·t`). -/
meta def mkSAddNatNamed (tE htE : Expr) (tneg : Bool) (tn td n : ℕ) : MetaM CNamed := do
  let he := mkAppN (mkConst ``s_add_nat_mk)
    #[tE, toExpr tneg, natLitShared tn, natLitShared td, natLitShared n, htE]
  cnamedConst he false (1 + 2 * n) 2 tneg tn td

/-- Named rectangle of `(ascPochhammer ℂ m).eval s` (`m ≥ 1`), a product of the named leaves
`s + i`. The radius stays zero until `renorm` caps the exact fields. -/
meta def mkPochNamed (tE htE : Expr) (tneg : Bool) (tn td m : ℕ) : MetaM CNamed := do
  unless 1 ≤ m do throwError "mkPochNamed: m must be at least 1"
  let s ← mkSNamed tE htE tneg tn td
  let heBase := mkApp (mkConst ``ascPochhammer_one_eval) s.z
  let mut acc ← cnamedOfEq (← lemmaLhs heBase) heBase s
  for i in [1:m] do
    let f ← mkSAddNatNamed tE htE tneg tn td i
    let prod ← cMulNamed acc f
    let heStep := mkAppN (mkConst ``ascPochhammer_succ_eval_c)
      #[natLitShared i, natLitShared (i + 1), s.z, reflBoolTrue]
    acc ← cnamedOfEq (← lemmaLhs heStep) heStep prod
    if i % checkpointStride == 0 then
      acc ← cnamedCheckpoint acc
  return acc

open Elab Term in
/-- `poch_named% tn td m D` : the named rectangle of `(ascPochhammer ℂ m).eval (½ + i·(tn/td))`
(with `t` carried as the canonical `sfrac`). -/
elab "poch_named% " tnn:num tdn:num mn:num : term => do
  let tn := tnn.getNat; let td := tdn.getNat
  let tE := sfracExpr false tn td
  let htE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) tE
  return (← mkPochNamed tE htE false tn td mn.getNat).proof

/-- Benchmark: the named enclosure of `(ascPochhammer ℂ 3).eval s` at `t = 14.1`. Reference
(mpmath `rf(s,3)`): `≈ -892.77 - 2722.146i`. -/
example := poch_named% 141 10 3

/-! ### The named zeta approximant -/

/-- Name the raw pair of a component rectangle as its `⟨re, im⟩` value
(`Complex.IsNear.mk`). -/
meta def cnamedOfMk (c : CNear) : MetaM CNamed := do
  let pf := mkAppN (mkConst ``Complex.IsNear.mk)
    #[c.re.x, c.im.x, toExpr c.re.neg, natLitShared c.re.cn,
      natLitShared c.re.cd, natLitShared c.re.rn, natLitShared c.re.rd, toExpr c.im.neg,
      natLitShared c.im.cn, natLitShared c.im.cd, natLitShared c.im.rn, natLitShared c.im.rd,
      c.re.proof, c.im.proof]
  let zmk := mkMkC c.re.x c.im.x
  return { z := zmk, proof := pf, re := c.re, im := c.im }

/-- Named rectangle of `(n:ℂ)^{-s}` at `s = ½ + i·t`: the cpow builder's rectangle, renamed
through `cpow_neg_s_mk`. -/
meta def mkCpowNegSNamed (tE htE : Expr) (tn td n D : ℕ) : MetaM CNamed := do
  let c ← withPhase "cpow: certificates" (mkCpowIntCNear n (-1) (-(tn : ℤ)) td D)
  withPhase "cpow: named assembly" do
    let he := mkAppN (mkConst ``cpow_neg_s_mk)
      #[tE, natLitShared tn, natLitShared td, natLitShared n, htE, reflBoolTrue]
    cnamedOfEq (← lemmaLhs he) he (← cnamedOfMk c)

/-- The `sfrac`-form Bernoulli value lemma `bern_real_k` for `bernoulli (2k)`, as
`(name, neg, num, den)` read off its statement. -/
meta def bernRealLemma (k : ℕ) : MetaM (Name × Bool × ℕ × ℕ) := do
  let nm := Name.mkStr1 "BSN" ++ Name.mkSimple ("bern_real_" ++ toString k)
  let some info := (← getEnv).find? nm
    | throwError "bernRealLemma: no Bernoulli value lemma for k = {k} (the generated table \
        covers 1 ≤ k ≤ 99; extend `derive_bern_real` in \
        `Enclosure.BinarySplit.Functions.Bernoulli`)"
  let some (_, _, rhs) := info.type.eq?
    | throwError "bernRealLemma: {nm} is not an equality"
  let args := rhs.getAppArgs
  unless rhs.isAppOfArity ``sfrac 3 do
    throwError "bernRealLemma: {nm} does not conclude in an `sfrac`"
  let neg ← match args[0]! with
    | .const ``Bool.true _ => pure true
    | .const ``Bool.false _ => pure false
    | _ => throwError "bernRealLemma: {nm} has a non-literal sign"
  let some bn ← getNatValue? args[1]!
    | throwError "bernRealLemma: {nm} has a non-literal numerator"
  let some bd ← getNatValue? args[2]!
    | throwError "bernRealLemma: {nm} has a non-literal denominator"
  return (nm, neg, bn, bd)

/-- Memo-reuse guard: whether every constant cited by the stored proofs exists in the current
environment (under parallel elaboration another command's aux lemmas may not). -/
meta def proofsInEnv (es : Array Expr) : MetaM Bool := do
  let env ← getEnv
  return es.all fun e ↦ e.getUsedConstants.all env.contains

/-- Build-once cache for enclosures of closed values: the enclosure proof is emitted as a
module aux lemma (`mkAuxLemma` dedupes by statement) and every use cites the constant. -/
meta def cachedNear (build : MetaM RNear) : MetaM RNear := do
  let r ← build
  let ty := mkAppN (mkConst ``Real.IsNear)
    #[r.x, toExpr r.neg, natLitShared r.cn, natLitShared r.cd, natLitShared r.rn, natLitShared r.rd]
  let nm ← withPhase "seal: mkAuxLemma" do mkAuxLemma [] ty r.proof
  return { r with proof := mkConst nm }

/-- `cachedNear build`, memoized under `key` in `cache`. -/
meta def memoCachedNear {κ : Type} [BEq κ] [Hashable κ] (cache : IO.Ref (Std.HashMap κ RNear))
    (key : κ) (build : MetaM RNear) : MetaM RNear := do
  if let some r := (← cache.get)[key]? then
    if ← proofsInEnv #[r.proof] then return r
  let r ← cachedNear build
  cache.modify (·.insert key r)
  return r

/-- `cachedNear build` for an enclosure at the endpoint `tE`, memoized under `key` in `cache` with
`tE` stored as a guard. -/
meta def memoCachedNearAt {κ : Type} [BEq κ] [Hashable κ]
    (cache : IO.Ref (Std.HashMap κ (Expr × RNear))) (key : κ) (tE : Expr) (build : MetaM RNear) :
    MetaM RNear := do
  if let some (tE', r) := (← cache.get).get? key then
    if tE' == tE && (← proofsInEnv #[r.proof]) then
      return r
  let r ← cachedNear build
  cache.modify (·.insert key (tE, r))
  return r

/-- `cachedNear` for a closed constant that depends only on the working precision (`log π`,
`(2π)⁻¹`, …): built and sealed once per `(tag, D)`, memoized in `sealedConstCache`. -/
meta def sealedConst (tag : String) (D : ℕ) (build : MetaM RNear) : MetaM RNear :=
  memoCachedNear sealedConstCache (tag, D) build

/-- Named rectangle of `zetaApproximant (½ + i·t) M N`, assembled in the folded form of
`zetaApproximant_eq_folded'`. -/
private meta def mkZetaApproxNamedCore (tE htE : Expr) (tn td M N D : ℕ) : MetaM CNamed := do
  unless 1 ≤ N do throwError "mkZetaApproxNamed: N must be at least 1"
  let s ← mkSNamed tE htE false tn td
  let sE := s.z
  -- head: ∑_{Ico 1 N} n^{-s}, accumulated through the named partial sum `headSumC` so each
  -- peel step's statement is a small application, then renamed onto the `Finset.sum` form once
  let head ← withPhase "zeta: head sum" do
    let mut head ← cnamedConst (mkApp (mkConst ``head_sum_c_base) sE) false 0 1 false 0 1
    let mut headStart := 1
    -- `1^{-s} = 1` exactly, so seed the accumulator at `headSumC s 2 = 1` (`head_sum_c_two`) and
    -- start the `cpow` leaves at `n = 2`.
    if 2 ≤ N then
      head ← cnamedConst (mkApp (mkConst ``head_sum_c_two) sE) false 1 1 false 0 1
      headStart := 2
    for n in [headStart:N] do
      let term ← withPhase "head: cpow leaf" (mkCpowNegSNamed tE htE tn td n D)
      let sum ← withPhase "head: add" (cAddNamed head term)
      let heStep := mkAppN (mkConst ``head_sum_c_succ)
        #[sE, natLitShared n, natLitShared (n + 1), reflBoolTrue, reflBoolTrue]
      let hLhs := mkApp2 (mkConst ``headSumC) sE (natLitShared (n + 1))
      head ← withPhase "head: rename" (cnamedOfEq hLhs heStep sum)
      if n % checkpointStride == 0 then
        head ← withPhase "head: checkpoint" (cnamedCheckpoint head)
    let heEq := mkApp2 (mkConst ``head_sum_c_eq) sE (natLitShared N)
    cnamedOfEq (← lemmaLhs heEq) heEq head
  -- tail: N/(s−1) + 1/2 + ∑_{Icc 1 M} coeff·poch·(N^{2k−1})⁻¹
  let tail ← withPhase "zeta: bernoulli tail" do
    let heDiv := mkAppN (mkConst ``N_div_s_sub_one_mk)
      #[tE, natLitShared tn, natLitShared td, natLitShared N, htE, reflBoolTrue, reflBoolTrue]
    let divLeaf ← cnamedConst heDiv true (2 * N * (td * td)) (td * td + 4 * (tn * tn))
      true (4 * N * (tn * td)) (td * td + 4 * (tn * tn))
    let halfLeaf ← cnamedConst (mkConst ``half_c_mk) false 1 2 false 0 1
    let mut bsum ← cnamedConst (mkApp2 (mkConst ``bern_sum_base) sE (natLitShared N)) false 0 1
      false 0 1
    -- incremental named Pochhammer (s)_{2k−1}
    let hePochBase := mkApp (mkConst ``ascPochhammer_one_eval) sE
    let mut poch ← cnamedOfEq (← lemmaLhs hePochBase) hePochBase s
    for k in [1:M+1] do
      if k > 1 then
        -- extend (s)_{2k−3} to (s)_{2k−1}: multiply by (s + (2k−3)) and (s + (2k−2))
        for i in [2*k-3, 2*k-2] do
          let f ← mkSAddNatNamed tE htE false tn td i
          let prod ← cMulNamed poch f
          let heStep := mkAppN (mkConst ``ascPochhammer_succ_eval_c)
            #[natLitShared i, natLitShared (i + 1), sE, reflBoolTrue]
          poch ← cnamedOfEq (← lemmaLhs heStep) heStep prod
        poch ← cnamedCheckpoint poch
      let (bLem, bneg, bn, bd) ← bernRealLemma k
      let F := Nat.factorial (2 * k)
      let hF ← mkNatEvalAux
        (mkApp (mkConst ``factNat) (natMulE (natLitShared 2) (natLitShared k))) F
      let coeffHe := mkAppN (mkConst ``bern_coeff_mk)
        #[natLitShared k, natLitShared bn, natLitShared bd, natLitShared F, toExpr bneg,
          mkConst bLem, hF, reflBoolTrue]
      let coeff ← cnamedConst coeffHe bneg bn (bd * F) false 0 1
      let Pw := N ^ (2 * k - 1)
      let hPw ← mkNatEvalAux (natPowE (natLitShared N) (natLitShared (2 * k - 1))) Pw
      let invHe := mkAppN (mkConst ``natCast_pow_inv_mk)
        #[natLitShared N, natLitShared (2 * k - 1), natLitShared Pw, hPw, reflBoolTrue]
      let ninv ← cnamedConst invHe false 1 Pw false 0 1
      let term ← cMulNamed (← cMulNamed coeff poch) ninv
      let sum ← cAddNamed bsum term
      let heStep := mkAppN (mkConst ``bern_sum_succ)
        #[sE, natLitShared N, natLitShared (k - 1), natLitShared k, natLitShared (2 * k - 1),
          reflBoolTrue, reflBoolTrue]
      bsum ← cnamedOfEq (← lemmaLhs heStep) heStep sum
      if k % checkpointStride == 0 then
        bsum ← cnamedCheckpoint bsum
    cAddNamed (← cAddNamed divLeaf halfLeaf) bsum
  withPhase "zeta: fold" do
    let nMs ← mkCpowNegSNamed tE htE tn td N D
    let folded ← cAddNamed head (← cMulNamed nMs tail)
    let heFold := mkAppN (mkConst ``zetaApproximant_eq_folded')
      #[sE, natLitShared M, natLitShared N, reflBoolTrue]
    let foldLhs := mkApp3 (mkConst ``zetaApproximant) sE (natLitShared M) (natLitShared N)
    cnamedOfEq foldLhs heFold folded

/-- `mkZetaApproxNamedCore` memoized in `zetaNamedCache` (keyed by `(M, N, tn, td, D)`, guarded
by `tE`). -/
meta def mkZetaApproxNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM CNamed := do
  let key := (M, N, tn, td, D)
  if let some (tE', z, proof, re, im) := (← zetaNamedCache.get).get? key then
    if tE' == tE && (← proofsInEnv #[proof, re.proof, im.proof]) then
      return { z, proof, re, im }
  let x ← mkZetaApproxNamedCore tE htE tn td M N D
  zetaNamedCache.modify (·.insert key (tE, x.z, x.proof, x.re, x.im))
  return x

open Elab Term in
/-- `zetaNamed% M N tn td D` : the rectangle enclosure of the named
`zetaApproximant (½ + i·(tn/td)) M N`. -/
elab "zetaNamed% " Mn:num Nn:num tnn:num tdn:num Dn:num : term => do
  let tn := tnn.getNat; let td := tdn.getNat
  let tE := sfracExpr false tn td
  let htE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) tE
  return (← mkZetaApproxNamed tE htE tn td Mn.getNat Nn.getNat Dn.getNat).proof

/-- Benchmark: the named `zetaApproximant (½ + 14.1i) 3 6` rectangle. Reference (mpmath, same
finite formula): `≈ 0.0045251353 - 0.0269845252i`. -/
example := zetaNamed% 3 6 141 10 100000000

/-! ### The named theta and Hardy `Z` approximants -/

/-- `congrArg` at `ℂ → ℂ`, raw. -/
meta def mkCongrArgC (f a b h : Expr) : Expr :=
  mkAppN (Expr.const ``congrArg [1, 1]) #[mkConst ``Complex, mkConst ``Complex, a, b, f, h]

/-- `Eq.trans` at `ℝ`, raw. -/
meta def mkEqTransR (a b c h1 h2 : Expr) : Expr :=
  mkAppN (Expr.const ``Eq.trans [1]) #[mkConst ``Real, a, b, c, h1, h2]

/-- The rectangle of `((r : ℝ) : ℂ)` from an enclosure of the real `r`. -/
meta def cnamedOfReal (r : RNear) : MetaM CNamed := do
  let rE := r.x
  let heRe := mkApp (mkConst ``Complex.ofReal_re) rE
  let reLhs := mkApp (mkConst ``Complex.re) (mkApp (mkConst ``Complex.ofReal) rE)
  let reP ← ofEqNearHe reLhs heRe r
  let zeroProof :=
      mkAppN (mkConst ``Real.IsNear.const) #[toExpr false, natLitShared 0, natLitShared 1]
  let zeroC : RNear :=
    { proof := zeroProof, x := mkSfracR false 0 1,
      neg := false, cn := 0, cd := 1, rn := 0, rd := 1 }
  let z := mkApp (mkConst ``Complex.ofReal) rE
  let imTy := mkApp (mkConst ``Complex.im) z
  let hZero := mkConst ``sfrac_zero_eq
  let heIm := mkEqTransR imTy (← lemmaLhs hZero) zeroC.x
    (mkApp (mkConst ``Complex.ofReal_im) rE) hZero
  -- `heIm : imTy = zeroC.x` (via `Eq.trans`), so its LHS is `imTy`, held here directly.
  let imP ← ofEqNearHe imTy heIm zeroC
  return cnamedOfParts z { re := reP, im := imP }

/-- Named complex inverse, through the reciprocal of `normSq z`. Needs `normSq z > 0` (true
for every `w + j`). -/
meta def cInvNamed (x : CNamed) (D : ℕ) : MetaM CNamed := do
  let nsqRaw ← addNear (← mulNear x.re x.re) (← mulNear x.im x.im)
  let heNsq := mkApp (mkConst ``Complex.normSq_eq_mul_add_mul) x.z
  let nsq ← ofEqNearHe (← lemmaLhs heNsq) heNsq nsqRaw
  -- the reciprocal image's dyadic grain is absolute, so scale the precision by the
  -- magnitude of `normSq`: the inverse (~1/normSq) then carries relative precision ~1/D,
  -- and the components stay ~1/D relative after the multiply by `z.re`/`z.im` (~√normSq).
  let inv ← mkInvImageNear nsq (D * max 1 (nsq.cn / nsq.cd))
  let heReInv := mkApp (mkConst ``Complex.inv_re_eq_mul) x.z
  let reP ← ofEqNearHe (← lemmaLhs heReInv) heReInv (← mulNear x.re inv)
  let heImInv := mkApp (mkConst ``Complex.inv_im_eq_mul) x.z
  let imP ← ofEqNearHe (← lemmaLhs heImInv) heImInv (← mulNear (← negNear x.im) inv)
  let zinv := reP.x.appArg!
  return cnamedOfParts zinv { re := reP, im := imP }

/-- Named rectangle of the leaf `w + j = ¼ + i·t/2 + j`. -/
meta def mkWNamed (tE htE : Expr) (tn td j : ℕ) : MetaM CNamed := do
  let he := mkAppN (mkConst ``w_shift_mk)
    #[tE, toExpr false, natLitShared tn, natLitShared td, natLitShared j, htE, reflBoolTrue]
  cnamedConst he false ((1 + 4 * j) * td) (4 * td) false (2 * tn) (4 * td)

/-- Named rectangle of `Complex.log (w + j)`: the `cLogNear` rectangle, renamed through
`congrArg Complex.log (w_shift_mk …)`. -/
meta def mkLogWNamed (tE htE : Expr) (tn td j D : ℕ) : MetaM CNamed := do
  let c ← withPhase "clog: certificates" (cLogNear ((1 + 4 * j) * td) (2 * tn) (4 * td) D)
  withPhase "clog: named assembly" do
    let zlog := c.re.x.appArg!
    let base := cnamedOfParts zlog c
    let hw := mkAppN (mkConst ``w_shift_mk)
      #[tE, toExpr false, natLitShared tn, natLitShared td, natLitShared j, htE, reflBoolTrue]
    let wSurface ← lemmaLhs hw
    let he := mkCongrArgC (mkConst ``Complex.log) wSurface zlog.appArg! hw
    -- `he : Complex.log wSurface = Complex.log zlog` (`congrArg`), so its LHS is `log wSurface`.
    cnamedOfEq (mkApp (mkConst ``Complex.log) wSurface) he base

/-- Named rectangle of `logGammaStirling M (w + N)`: `(z−½)·log z − z + ½·(log 2π : ℂ)` plus
the exact correction sum, every leaf named at its surface form. -/
meta def mkStirlingNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM CNamed := do
  let wN ← mkWNamed tE htE tn td N
  let wE := wN.z
  let logW ← mkLogWNamed tE htE tn td N D
  -- The Riemann–Siegel case uses N = 0 : `riemannSiegelThetaApproximant 2 0 t`
  let (heZmh, zNeg, zCn) :=
    if N == 0 then
      (mkAppN (mkConst ``w_sub_half_zero_mk)
        #[tE, toExpr false, natLitShared tn, natLitShared td, htE, reflBoolTrue], true, td)
    else
      (mkAppN (mkConst ``w_sub_half_mk)
        #[tE, toExpr false, natLitShared tn, natLitShared td, natLitShared N, htE,
          reflBoolTrue, reflBoolTrue], false, (4 * N - 1) * td)
  let zmh ← cnamedConst heZmh zNeg zCn (4 * td) false (2 * tn) (4 * td)
  let mut acc ← cSubNamed (← cMulNamed zmh logW) wN
  -- ½·(log 2π : ℂ)
  let log2pi ← sealedConst "log 2π" D do
    let heLog2pi := mkConst ``log_two_pi_eq
    ofEqNearHe (← lemmaLhs heLog2pi) heLog2pi
      (← mkLogImageNear (← mulNear (← mkConstNear 2 1) (← mkPiNear D)) D)
  let log2piC ← cnamedOfReal log2pi
  let halfC ← cnamedConst (mkConst ``half_c_mk) false 1 2 false 0 1
  acc ← cAddNamed acc (← cMulNamed halfC log2piC)
  -- the correction sum
  let mut ssum ← cnamedConst (mkApp (mkConst ``stirling_sum_base) wE) false 0 1 false 0 1
  let hePowOne := mkApp (mkConst ``pow_one_c) wE
  let mut wpow ← cnamedOfEq (← lemmaLhs hePowOne) hePowOne wN
  for k in [1:M+1] do
    if k > 1 then
      for i in [2*k-2, 2*k-1] do
        let prod ← cMulNamed wpow wN
        let heStep := mkAppN (mkConst ``pow_succ_c)
          #[wE, natLitShared (i - 1), natLitShared i, reflBoolTrue]
        wpow ← cnamedOfEq (← lemmaLhs heStep) heStep prod
      wpow ← cnamedCheckpoint wpow
    let winv ← cInvNamed wpow D
    let heZpow := mkAppN (mkConst ``zpow_one_sub_two_mul)
      #[wE, natLitShared k, natLitShared (2 * k - 1), reflBoolTrue, reflBoolTrue]
    let wz ← cnamedOfEq (← lemmaLhs heZpow) heZpow winv
    let (bLem, bneg, bn, bd) ← bernRealLemma k
    let coeffHe := mkAppN (mkConst ``stirling_coeff_mk)
      #[natLitShared k, natLitShared bn, natLitShared bd, toExpr bneg, mkConst bLem,
        reflBoolTrue, reflBoolTrue]
    let coeff ← cnamedConst coeffHe bneg bn (bd * (2 * k * (2 * k - 1))) false 0 1
    let term ← cMulNamed coeff wz
    let sum ← cAddNamed ssum term
    let heStep := mkAppN (mkConst ``stirling_sum_succ)
      #[wE, natLitShared (k - 1), natLitShared k, reflBoolTrue]
    ssum ← cnamedOfEq (← lemmaLhs heStep) heStep sum
    if k % checkpointStride == 0 then
      ssum ← cnamedCheckpoint ssum
  acc ← cAddNamed acc ssum
  -- rename the assembled body onto the compact `logGammaStirling M (w+N)` through a cited
  -- equality, so the kernel checks the gamma-series expansion once, in that lemma
  let heStir := mkAppN (mkConst ``logGammaStirling_unfold) #[natLitShared M, wE]
  cnamedOfEq (← lemmaLhs heStir) heStir acc

/-- Enclosure of the named theta approximant
`(logGammaStirling M (w+N) − ∑_{j<N} log(w+j)).im − t/2·log π`. -/
meta def mkThetaNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear := do
  let S ← withPhase "theta: stirling" (mkStirlingNamed tE htE tn td M N D)
  let L ← withPhase "theta: log sum" do
    let mut L ← cnamedConst (mkApp (mkConst ``log_sum_c_base) tE) false 0 1 false 0 1
    for j in [0:N] do
      let lj ← withPhase "logsum: log leaf" (mkLogWNamed tE htE tn td j D)
      let sum ← withPhase "logsum: add" (cAddNamed L lj)
      let heStep := mkAppN (mkConst ``log_sum_c_succ)
        #[tE, natLitShared j, natLitShared (j + 1), reflBoolTrue]
      let lLhs := mkApp2 (mkConst ``logSumC) tE (natLitShared (j + 1))
      L ← withPhase "logsum: rename" (cnamedOfEq lLhs heStep sum)
      if (j + 1) % checkpointStride == 0 then
        L ← withPhase "logsum: checkpoint" (cnamedCheckpoint L)
    let heLogEq := mkApp2 (mkConst ``log_sum_c_eq) tE (natLitShared N)
    cnamedOfEq (← lemmaLhs heLogEq) heLogEq L
  withPhase "theta: logπ + assemble" do
    let diff ← cSubNamed S L
    let heTHalf := mkAppN (mkConst ``t_half_eq)
      #[tE, toExpr false, natLitShared tn, natLitShared td, htE]
    let tHalf ← ofEqNearHe (← lemmaLhs heTHalf) heTHalf (← mkConstNear tn (2 * td))
    let logPi ← sealedConst "log π" D do mkLogImageNear (← mkPiNear D) D
    subNear diff.im (← mulNear tHalf logPi)

/-- Enclosure of the named Hardy `Z` approximant `Re(e^{iθ̃}·ζ̃)`, renamed through
`re_exp_mul`. -/
meta def mkHardyZNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear := do
  -- the theta shift is `thetaShift M = 2 * M` (height-independent), decoupled from the zeta
  -- cutoff N
  let θ ← mkThetaNamed tE htE tn td M (2 * M) D
  let ζ ← mkZetaApproxNamed tE htE tn td M N D
  withPhase "Zeta.hardyZ: trig + assemble" do
    let c ← mkCosImageNear θ D
    let s ← mkSinImageNear θ D
    let raw ← subNear (← mulNear c ζ.re) (← mulNear s ζ.im)
    let θE := θ.x
    let he := mkApp2 (mkConst ``re_exp_mul) θE ζ.z
    ofEqNearHe (← lemmaLhs he) he raw

open Elab Term in
/-- `thetaNamed% M N tn td D` : an enclosure of the named theta approximant. -/
elab "thetaNamed% " Mn:num Nn:num tnn:num tdn:num Dn:num : term => do
  let tn := tnn.getNat; let td := tdn.getNat
  let tE := sfracExpr false tn td
  let htE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) tE
  return (← mkThetaNamed tE htE tn td Mn.getNat Nn.getNat Dn.getNat).proof

/-- Benchmark: the named `θ̃` at `t = 14.1`, `M = 3`, `N = 6` (the surface expression of the
Hardy `Z` phase). Reference: `≈ -1.7427221027`. -/
example := thetaNamed% 3 6 141 10 100000000

open Elab Term in
/-- `hardyZNamed% M N tn td D` : an enclosure of the named Hardy `Z` approximant body. -/
elab "hardyZNamed% " Mn:num Nn:num tnn:num tdn:num Dn:num : term => do
  let tn := tnn.getNat; let td := tdn.getNat
  let tE := sfracExpr false tn td
  let htE := mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) tE
  return (← mkHardyZNamed tE htE tn td Mn.getNat Nn.getNat Dn.getNat).proof

/-- Benchmark: the named Hardy `Z` value `Re(e^{iθ̃}·ζ̃)` at `t = 14.1`, `M = 3`, `N = 6`
(definitionally `hardyZApproximantEM 3 6 14.1`). Reference: `≈ -0.0273608563`. -/
example := hardyZNamed% 3 6 141 10 100000000

/-! ### The named error bound and the certificate tactics -/

/-- `Real.IsNear.of_eq` with the left side supplied directly and `he` a `rfl`-style proof, for
renaming a reducible application (`hardyZApproximantEM …`, `hardyZErrorBoundStrong …`) onto its
assembled body. -/
meta def ofEqNearAt (x he : Expr) (r : RNear) : MetaM RNear := do
  let proof := mkAppN (mkConst ``Real.IsNear.of_eq)
    #[x, r.x, toExpr r.neg, natLitShared r.cn, natLitShared r.cd,
      natLitShared r.rn, natLitShared r.rd, he, r.proof]
  return { r with proof, x }

/-- `Eq.refl` at `ℝ` on the given expression, raw. -/
meta def mkReflR (e : Expr) : Expr :=
  mkApp2 (Expr.const ``Eq.refl [1]) (mkConst ``Real) e

/-- Named real power `x^m` (`m ≥ 1`) by a linear `pow_succ_r` chain over `mulNear`. -/
meta def mkRPowNamed (base : RNear) (m : ℕ) : MetaM RNear := do
  unless 1 ≤ m do throwError "mkRPowNamed: m must be at least 1"
  let bE := base.x
  let hePowOne := mkApp (mkConst ``pow_one_r) bE
  let mut acc ← ofEqNearHe (← lemmaLhs hePowOne) hePowOne base
  for i in [2:m+1] do
    let prod ← mulNear acc base
    let heStep := mkAppN (mkConst ``pow_succ_r)
      #[bE, natLitShared (i - 1), natLitShared i, reflBoolTrue]
    acc ← ofEqNearHe (← lemmaLhs heStep) heStep prod
    if i % checkpointStride == 0 then
      acc ← cachedNear (pure acc)
  return acc

/-- Named `‖z‖`, as the square root of the componentwise product sum. -/
meta def mkNormNamed (x : CNamed) (D : ℕ) : MetaM RNear := do
  let nsq ← addNear (← mulNear x.re x.re) (← mulNear x.im x.im)
  let sq ← mkSqrtImageNear nsq D
  let he := mkApp (mkConst ``norm_eq_sqrt_mul_add) x.z
  ofEqNearHe (← lemmaLhs he) he sq

/-- Named enclosure of `(2π)^{2M}`, the power both theta error bounds divide by. -/
meta def mkTwoPiPowNamed (M D : ℕ) : MetaM RNear := do
  let heTwoPi := mkConst ``two_pi_eq
  let twoPi ← ofEqNearHe (← lemmaLhs heTwoPi) heTwoPi (← mulNear (← mkConstNear 2 1) (← mkPiNear D))
  mkRPowNamed twoPi (2 * M)

/-- Named enclosure of `riemannSiegelThetaStirlingErrorBound M N`: the exact rational times the
reciprocal image of the named `(2π)^{2M}` power. -/
meta def mkThetaErrNamed (M N D : ℕ) : MetaM RNear := do
  let piPow ← mkTwoPiPowNamed M D
  let A := Nat.factorial (2 * M + 1) * 4 ^ (2 * M)
  let B := 2 * M * (1 + 4 * N) ^ (2 * M)
  let raw ← mulNear (← mkConstNear A B) (← mkInvImageNear piPow D)
  let twoM := natMulE (natLitShared 2) (natLitShared M)
  let hA ← mkNatEvalAux
    (natMulE (mkApp (mkConst ``factNat) (natSuccE twoM)) (natPowE (natLitShared 4) twoM)) A
  let hB ← mkNatEvalAux
    (natMulE twoM (natPowE (natSuccE (natMulE (natLitShared 4) (natLitShared N)))
      twoM)) B
  let he := mkAppN (mkConst ``theta_err_eq)
    #[natLitShared M, natLitShared N, natLitShared A, natLitShared B, hA, hB, reflBoolTrue]
  let errLhs := mkApp2 (mkConst ``riemannSiegelThetaStirlingErrorBound)
    (natLitShared M) (natLitShared N)
  ofEqNearHe errLhs he raw

/-- Named enclosure of `riemannSiegelThetaStirlingErrorBound' M N t` at `t = tn/td`: the exact
rational from `theta_err_eq'` times the reciprocal image of the named `(2π)^{2M}` power. -/
meta def mkThetaErrNamed' (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear := do
  let piPow ← mkTwoPiPowNamed M D
  let A := Nat.factorial (2 * M + 1) * 2 ^ (2 * M + 1) * (16 * td ^ 2) ^ M
  let B := 2 * M * ((4 * N + 1) ^ 2 * td ^ 2 + 4 * tn ^ 2) ^ M
  let raw ← mulNear (← mkConstNear A B) (← mkInvImageNear piPow D)
  let twoM := natMulE (natLitShared 2) (natLitShared M)
  let tdSq := natMulE (natLitShared td) (natLitShared td)
  let fourN1 := natSuccE (natMulE (natLitShared 4) (natLitShared N))
  let hA ← mkNatEvalAux
    (natMulE
      (natMulE (mkApp (mkConst ``factNat) (natSuccE twoM))
        (natPowE (natLitShared 2) (natSuccE twoM)))
      (natPowE (natMulE (natLitShared 16) tdSq) (natLitShared M))) A
  let hB ← mkNatEvalAux
    (natMulE twoM (natPowE
      (natAddE (natMulE (natMulE fourN1 fourN1) tdSq)
        (natMulE (natLitShared 4) (natMulE (natLitShared tn) (natLitShared tn))))
      (natLitShared M))) B
  let he := mkAppN (mkConst ``theta_err_eq')
    #[tE, natLitShared tn, natLitShared td, natLitShared M, natLitShared N, natLitShared A,
      natLitShared B, htE, hA, hB, reflBoolTrue, reflBoolTrue]
  let errLhs := mkApp3 (mkConst ``riemannSiegelThetaStirlingErrorBound')
    (natLitShared M) (natLitShared N) tE
  ofEqNearHe errLhs he raw

/-- Named enclosure of the strengthened Hardy `Z` error bound
`θerr·‖ζ̃‖ + zetaRemainderBound (½+it) M N`. -/
meta def mkErrStrongNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear := do
  -- the theta error uses the height-independent shift `thetaShift M = 2 * M`
  let θerr ← withPhase "err: theta error bound" (mkThetaErrNamed M (2 * M) D)
  let ζ ← mkZetaApproxNamed tE htE tn td M N D
  let normζ ← withPhase "err: ‖ζ̃‖" (mkNormNamed ζ D)
  withPhase "err: zeta remainder bound" do
    -- zetaRemainderBound: ‖s+(2M+1)‖ / (s.re+(2M+1)) * ‖coeff·poch·N^{-s-(2M+1)}‖
    let m := 2 * M + 1
    -- the remainder term has magnitude ~N^{-(2M+3/2)}; its rectangle and norm need precision
    -- well below that scale or the square-sum enclosure straddles zero
    let Dr := D * N ^ (2 * M + 2)
    let sAdd ← mkSAddNatNamed tE htE false tn td m
    let normA ← mkNormNamed sAdd D
    let (bLem, bneg, bn, bd) ← bernRealLemma (M + 1)
    let F := Nat.factorial (2 * (M + 1))
    let hF ← mkNatEvalAux
      (mkApp (mkConst ``factNat) (natMulE (natLitShared 2) (natLitShared (M + 1)))) F
    let coeffHe := mkAppN (mkConst ``bern_coeff_mk)
      #[natLitShared (M + 1), natLitShared bn, natLitShared bd, natLitShared F, toExpr bneg,
        mkConst bLem, hF, reflBoolTrue]
    let coeff ← cnamedConst coeffHe bneg bn (bd * F) false 0 1
    let poch ← mkPochNamed tE htE false tn td m
    let P := N ^ (1 + 2 * m)
    let npowRaw ← mkCpowIntCNear N (-(1 + 2 * m : ℤ)) (-(tn : ℤ)) td Dr
    let hP ← mkNatEvalAux
      (natPowE (natLitShared N) (natSuccE (natMulE (natLitShared 2) (natLitShared m)))) P
    let heNp := mkAppN (mkConst ``cpow_neg_s_sub_mk)
      #[tE, natLitShared tn, natLitShared td, natLitShared N, natLitShared m, natLitShared P, htE,
        reflBoolTrue, hP]
    let npow ← cnamedOfEq (← lemmaLhs heNp) heNp (← cnamedOfMk npowRaw)
    let inner ← cMulNamed (← cMulNamed coeff poch) npow
    let normC ← mkNormNamed inner Dr
    let zrbRaw ← mulNear (← mulNear normA (← mkConstNear 2 (1 + 2 * m))) normC
    let heZrb := mkAppN (mkConst ``zrb_shape_eq)
      #[normA.x, normC.x, tE, natLitShared m]
    let zrb ← ofEqNearHe (← lemmaLhs heZrb) heZrb zrbRaw
    addNear (← mulNear θerr normζ) zrb

/-- Read a `ℕ` literal, through `whnf` when needed: handles a wrapper such as a structure
projection of a literal instance (`interval₁.leftBernoulli`) or a reducible def, and the
`OfNat` numeral forms (via the engine's `evalNat`). -/
meta def natLit? (e : Expr) : MetaM (Option ℕ) := do
  try return some (← evalNat e)
  catch _ =>
  try return some (← evalNat (← whnfR e))
  catch _ => return none

/-- Reduce `e` until its head is the constant `c` (a no-op when it already is; `e` unchanged
when the head never appears). Lets the certificate tactics parse goals stated through
wrappers like `ZeroInterval.leftVal I`. -/
meta def headTo (e : Expr) (c : Name) : MetaM Expr := do
  if e.getAppFn.constName? == some c then return e
  return (← whnfUntil e c).getD e

/-- `recognizeRat`, retrying through `whnf` for wrapped arguments (structure projections of
literal instances); also returns the expression the recogniser succeeded on, which is what
the enclosure builders must be handed. -/
meta def recognizeRat' (e : Expr) : MetaM (Bool × ℕ × ℕ × Expr × Expr) := do
  try
    let (n, u, v, h) ← recognizeRat e
    return (n, u, v, h, e)
  catch _ =>
    let e' ← whnfR e
    let (n, u, v, h) ← recognizeRat e'
    return (n, u, v, h, e')

/-- The cached enclosure of `hardyZApproximantEM M N t`, stated at the canonical application
and memoized per `(M, N, t, D)` in `hardyZNamedCache`. -/
meta def mkHardyZCached (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear :=
  memoCachedNearAt hardyZNamedCache (M, N, tn, td, D) tE do
    let r ← mkHardyZNamed tE htE tn td M N D
    let xC := mkAppN (mkConst ``hardyZApproximantEM) #[natLitShared M, natLitShared N, tE]
    ofEqNearAt xC (mkReflR r.x) r

/-- A resolved Hardy-`Z` site: the subject expression `x`, the literal cutoffs `M`, `N`, and the
endpoint `tE = sfrac false tn td` with its proof `htE` and numeric height `tn/td`. Filled by
parsing the goal (`resolveHardyZSite`) or straight from a row (`build_certs`). -/
structure HardyZSite where
  /-- The subject expression the enclosure is transported onto. -/
  x : Expr
  /-- Bernoulli-term count. -/
  M : ℕ
  /-- Euler–Maclaurin cutoff. -/
  N : ℕ
  /-- Height numerator. -/
  tn : ℕ
  /-- Height denominator. -/
  td : ℕ
  /-- Proof `tE = sfrac false tn td`. -/
  htE : Expr
  /-- The endpoint expression `sfrac false tn td`. -/
  tE : Expr

/-- The default working precision for a site, scaled with the height since enclosure noise grows
about linearly in `t`. -/
meta def siteD (s : HardyZSite) (D? : Option ℕ) : ℕ :=
  D?.getD (100000000 * max 1 (s.tn / (30 * s.td)))

open Elab Tactic Term in
/-- Parse a subject expression `x` (reducing to `hardyZApproximantEM M N t`) into its resolved
`HardyZSite`; rejects a nonpositive `t`. -/
meta def resolveHardyZSite (x : Expr) (who : String) : MetaM HardyZSite := do
  let x' ← headTo x ``hardyZApproximantEM
  let args := x'.getAppArgs
  unless x'.getAppFn.constName? == some ``hardyZApproximantEM && args.size == 3 do
    throwError "{who}: expected `hardyZApproximantEM M N t`, got {x}"
  let some M ← natLit? args[0]! | throwError "{who}: M must be a literal"
  let some N ← natLit? args[1]! | throwError "{who}: N must be a literal"
  let (tneg, tn, td, htE, tE) ← recognizeRat' args[2]!
  if tneg || tn == 0 then throwError "{who}: t must be positive"
  return { x, M, N, tn, td, htE, tE }

/-- The named enclosure of one site's Hardy-`Z` value, transported onto the site's subject `x`. -/
meta def mkHardyZSiteNear (s : HardyZSite) (D? : Option ℕ := none) : MetaM RNear := do
  let r ← withPhase s!"Zeta.hardyZ enclosure t={s.tn}/{s.td}"
    (mkHardyZCached s.tE s.htE s.tn s.td s.M s.N (siteD s D?))
  ofEqNearAt s.x (mkReflR r.x) r

/-- A proof of `aE * bE < 0` from enclosures `ra` of `aE` and `rb` of `bE` that clear zero with
opposite signs (`neg_val`/`pos_val`); `who` prefixes the same-sign error. -/
meta def mulNegOfSignsNear (who : String) (ra : RNear) (aE : Expr) (rb : RNear) (bE : Expr) :
    MetaM Expr := do
  let mkSignPf (x : Expr) (r : RNear) : Expr :=
    mkAppN (mkConst (if r.neg then ``Real.IsNear.neg_val else ``Real.IsNear.pos_val))
      #[x, natLitShared r.cn, natLitShared r.cd, natLitShared r.rn, natLitShared r.rd, r.proof,
        reflBoolTrue, reflBoolTrue, reflBoolTrue]
  if ra.neg && !rb.neg then
    return mkAppN (mkConst ``mul_neg_of_neg_pos_r) #[aE, bE, mkSignPf aE ra, mkSignPf bE rb]
  else if !ra.neg && rb.neg then
    return mkAppN (mkConst ``mul_neg_of_pos_neg_r) #[aE, bE, mkSignPf aE ra, mkSignPf bE rb]
  else throwError "{who}: both endpoint values have the same sign"

/-- Core of `hardy_sign_change` on two resolved sites: enclose both, extract their signs
(`neg_val`/`pos_val`), and combine into `sa.x * sb.x < 0`. -/
meta def hardySignChangeSites (sa sb : HardyZSite) (D? : Option ℕ := none) : MetaM Expr := do
  let mkSide (s : HardyZSite) : MetaM (RNear × Expr) := do
    let named ← mkHardyZSiteNear s D?
    unless named.rn * named.cd < named.cn * named.rd do
      throwError "hardy_sign_change: the enclosure at {s.tE} does not separate from zero; \
        increase M or N"
    return (named, s.x)
  let (ra, aE) ← mkSide sa
  let (rb, bE) ← mkSide sb
  mulNegOfSignsNear "hardy_sign_change" ra aE rb bE

/-- Goal-facing `hardy_sign_change` core: parse both product factors into sites, then delegate to
`hardySignChangeSites`. -/
meta def hardySignChangeCore (a b : Expr) (D? : Option ℕ := none) : MetaM Expr := do
  hardySignChangeSites (← resolveHardyZSite a "hardy_sign_change")
    (← resolveHardyZSite b "hardy_sign_change") D?

open Elab Tactic Term in
/-- `hardy_sign_change` closes `hardyZApproximantEM M N tl * hardyZApproximantEM M N tr < 0`,
with `t` in any recognised rational surface form; each factor may sit behind a reducible wrapper
(e.g. `ZeroInterval.leftVal I` for a literal `I`). -/
elab "hardy_sign_change" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr LT.lt _ _ lhs _ := ty
    | throwError "hardy_sign_change: goal must be `Z̃(l) * Z̃(r) < 0`"
  let_expr HMul.hMul _ _ _ _ a b := lhs
    | throwError "hardy_sign_change: expected a product on the left"
  let pf ← hardySignChangeCore a b
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

/-- A `norm_gt_of_isNear` proof of `‖s.x‖ > bnd` on a resolved site `s`, for a bound `bnd`
enclosing as `hardyZErrorBoundStrong M N t`. -/
meta def hardyErrOkSite (s : HardyZSite) (bnd : Expr) (D? : Option ℕ := none) : MetaM Expr := do
  let D := siteD s D?
  let hx ← mkHardyZSiteNear s (some D)
  let rE ← withPhase s!"errStrong enclosure t={s.tn}/{s.td}"
    (cachedNear (mkErrStrongNamed s.tE s.htE s.tn s.td s.M s.N D))
  let he ← ofEqNearAt bnd (mkReflR rE.x) rE
  -- meta-check the margin before emitting the kernel condition
  unless normGtMarginOk hx he do
    throwError "hardy_error_ok_full: the error bound is not below the value's margin; \
      increase M or N"
  return mkNormGtOfIsNear s.x bnd hx he

/-- Core of `hardy_error_ok_full` on a resolved site `s`: a proof of
`‖s.x‖ > hardyZErrorBoundEM M N t`. -/
meta def hardyErrOkFullSite (s : HardyZSite) (D? : Option ℕ := none) : MetaM Expr := do
  let strong :=
      mkAppN (mkConst ``hardyZErrorBoundStrong) #[natLitShared s.M, natLitShared s.N, s.tE]
  let pfStrong ← hardyErrOkSite s strong D?
  let rhs := mkAppN (mkConst ``hardyZErrorBoundEM) #[natLitShared s.M, natLitShared s.N, s.tE]
  let glue := mkAppN (mkConst ``hardyZErrorBoundEM_le_strong)
    #[natLitShared s.M, natLitShared s.N, s.tE, reflBoolTrue]
  -- `hardyErrOkSite` proves `‖s.x‖ > strong`; build `‖s.x‖` directly (the ℝ `Norm` instance is
  -- `Real.norm`).
  let normX := mkAppN (mkConst ``Norm.norm [0]) #[mkConst ``Real, mkConst ``Real.norm, s.x]
  return mkAppN (mkConst ``gt_trans_le) #[normX, strong, rhs, glue, pfStrong]

open Elab Tactic Term in
/-- `hardy_error_ok_full` closes `‖hardyZApproximantEM M N t‖ > hardyZErrorBoundEM M N t`, the
working bound with the opaque `‖zetaRemainder‖`. -/
elab "hardy_error_ok_full" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr GT.gt _ _ lhs _ := ty
    | throwError "hardy_error_ok_full: goal must be `‖Z̃(t)‖ > hardyZErrorBoundEM M N t`"
  let_expr Norm.norm _ _ x := lhs
    | throwError "hardy_error_ok_full: expected a norm on the left"
  let pf ← hardyErrOkFullSite (← resolveHardyZSite x "hardy_error_ok_full")
  liftMetaFinishingTactic (·.assign pf)

/-! ### Gram-point certificates -/

/-- Named enclosure of `↑idx · π` (`natCast_mul_pi_eq` renames the constant-times-`π`
product). -/
meta def mkIdxPiNamed (idx D : ℕ) : MetaM RNear := do
  let raw ← mulNear (← mkConstNear idx 1) (← mkPiNear D)
  let he := mkApp (mkConst ``natCast_mul_pi_eq) (natLitShared idx)
  ofEqNearHe (← lemmaLhs he) he raw

/-- Named enclosure of `riemannSiegelThetaApproximant M N t`: `mkThetaNamed` renamed through
`riemannSiegelThetaApproximant_named`. -/
meta def mkThetaApproxNamed (tE htE : Expr) (tn td M N D : ℕ) : MetaM RNear := do
  let θ ← mkThetaNamed tE htE tn td M N D
  let x := mkAppN (mkConst ``riemannSiegelThetaApproximant) #[natLitShared M, natLitShared N, tE]
  -- cite the proven unfolding of the approximant so the kernel matches the rename by the lemma's
  -- stated type
  let he := mkAppN (mkConst ``riemannSiegelThetaApproximant_named)
    #[natLitShared M, natLitShared N, tE]
  ofEqNearAt x he θ

open Elab Tactic in
/-- `gram_bound` closes a Gram-point certificate obligation
`↑idx * π − riemannSiegelThetaApproximant M N t > riemannSiegelThetaStirlingErrorBound' M N t`
(the left form) or the mirrored
`riemannSiegelThetaApproximant M N t − ↑idx * π > riemannSiegelThetaStirlingErrorBound' M N t`
(the right form), with `t` in any recognised rational surface form. -/
elab "gram_bound" : tactic => do
  let ty ← (← getMainGoal).getType
  let_expr GT.gt _ _ lhs rhs := ty
    | throwError "gram_bound: goal must be `… > riemannSiegelThetaStirlingErrorBound' M N t`"
  let rargs := rhs.getAppArgs
  unless rhs.getAppFn.constName? == some ``riemannSiegelThetaStirlingErrorBound'
      && rargs.size == 3 do
    throwError "gram_bound: RHS must be `riemannSiegelThetaStirlingErrorBound' M N t`"
  let some M ← natLit? rargs[0]! | throwError "gram_bound: M must be a literal"
  let some N ← natLit? rargs[1]! | throwError "gram_bound: N must be a literal"
  let_expr HSub.hSub _ _ _ _ a b := lhs
    | throwError "gram_bound: LHS must be a difference"
  let a' ← headTo a ``riemannSiegelThetaApproximant
  let b' ← headTo b ``riemannSiegelThetaApproximant
  let isTheta (x : Expr) : Bool :=
    x.getAppFn.constName? == some ``riemannSiegelThetaApproximant
  let (thetaE, piE, thetaLeft) := if isTheta a' then (a', b', true) else (b', a', false)
  let targs := thetaE.getAppArgs
  unless isTheta thetaE && targs.size == 3 do
    throwError "gram_bound: expected `riemannSiegelThetaApproximant M N t` in the difference"
  let some M' ← natLit? targs[0]!
    | throwError "gram_bound: the approximant M must be a literal"
  let some N' ← natLit? targs[1]!
    | throwError "gram_bound: the approximant N must be a literal"
  unless M' == M && N' == N do
    throwError "gram_bound: (M, N) differ between the approximant and the error bound"
  let (tneg, tn, td, htE, tE) ← recognizeRat' targs[2]!
  if tneg || tn == 0 then throwError "gram_bound: t must be positive"
  let (eneg, en, ed, _, _) ← recognizeRat' rargs[2]!
  unless !eneg && en == tn && ed == td do
    throwError "gram_bound: t differs between the approximant and the error bound"
  -- height-scaled precision; see `hardy_sign_change`
  let D := 100000000 * max 1 (tn / (30 * td))
  let_expr HMul.hMul _ _ _ _ cE pE := piE
    | throwError "gram_bound: expected `↑idx * π` in the difference"
  unless pE.isConstOf ``Real.pi do
    throwError "gram_bound: expected `π` on the right of the index product"
  let_expr Nat.cast _ _ nE := cE
    | throwError "gram_bound: expected a `ℕ`-cast Gram index"
  let some idx ← natLit? nE | throwError "gram_bound: the Gram index must be a literal"
  let θ ← mkThetaApproxNamed tE htE tn td M N D
  let ip ← mkIdxPiNamed idx D
  let x ← if thetaLeft then subNear θ ip else subNear ip θ
  let e ← mkThetaErrNamed' tE htE tn td M N D
  -- meta-check the margin before emitting the kernel condition
  let q (neg : Bool) (cn cd : ℕ) : ℚ := (if neg then -1 else 1) * (cn : ℚ) / cd
  let xLo := q x.neg x.cn x.cd - (x.rn : ℚ) / x.rd
  let eUp := q e.neg e.cn e.cd + (e.rn : ℚ) / e.rd
  unless eUp < xLo do
    throwError "gram_bound: the theta margin does not clear the error bound; \
      widen the bracket or increase M or N"
  let pf := mkAppN (mkConst ``gt_of_isNear)
    #[lhs, rhs, toExpr x.neg, toExpr e.neg, natLitShared x.cn, natLitShared x.cd, natLitShared x.rn,
      natLitShared x.rd, natLitShared e.cn, natLitShared e.cd, natLitShared e.rn, natLitShared e.rd,
      x.proof, e.proof, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue]
  liftMetaFinishingTactic (·.assign pf)

/-! ### Smoke tests

The Euler–Maclaurin tactics that `gen_gram_certificates.py` emits for a Gram block below the
Riemann–Siegel range, on the bracket `[14.1, 14.2]` of the first zero. -/

example : hardyZApproximantEM 3 6 14.1 * hardyZApproximantEM 3 6 14.2 < 0 := by
  hardy_sign_change

example : ‖hardyZApproximantEM 3 6 14.1‖ > hardyZErrorBoundEM 3 6 14.1 := by
  hardy_error_ok_full

end BSN
