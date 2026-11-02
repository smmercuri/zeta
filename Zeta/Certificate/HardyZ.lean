module

public import Enclosure.BinarySplit.Tactic.Enclosures
public import Zeta.Certificate.Cpow

/-!
# Process-level memo caches for the Hardy `Z` named builders

The `zetaNamedCache` / `hardyZNamedCache` refs back the memoized zeta and Hardy `Z` enclosure
builders defined in `Zeta.Certificate.Named`. They live here, in a module `Named` imports, because
an `initialize` declaration cannot be evaluated in its own module. Keys are `(M, N, tn, td, D)`; the
values carry the requested surface `tE` as a guard alongside the built enclosure data, so several
obligations at the same `t` share one MetaM-side construction.
-/
@[expose] public section


namespace BSN
open Enclosure

open Lean Meta

/-- Memo for the named zeta approximant rectangle: value is
`(tE, z, proof, re, im)`: the fields of `Named`'s `CNamed` plus the `tE` guard. -/
initialize zetaNamedCache :
    IO.Ref (Std.HashMap (ℕ × ℕ × ℕ × ℕ × ℕ) (Expr × Expr × Expr × RNear × RNear)) ←
  IO.mkRef ∅

/-- Memo for the cached `hardyZApproximantEM` enclosure: value is `(tE, r)`; `r.proof` is a
single aux-lemma constant, so a hit skips the whole MetaM rebuild. -/
initialize hardyZNamedCache : IO.Ref (Std.HashMap (ℕ × ℕ × ℕ × ℕ × ℕ) (Expr × RNear)) ←
  IO.mkRef ∅

initialize hardyZNamedCacheRS : IO.Ref (Std.HashMap (ℕ × ℕ × ℕ) (Expr × RNear)) ←
  IO.mkRef ∅

/-- Memo for the cached linear-free `hardyZApproximantRS₀` enclosure, keyed like
`hardyZNamedCacheRS`. -/
initialize hardyZNamedCacheRS₀ : IO.Ref (Std.HashMap (ℕ × ℕ × ℕ) (Expr × RNear)) ←
  IO.mkRef ∅

initialize invSqrtNatCache : IO.Ref (Std.HashMap (ℕ × ℕ) RNear) ← IO.mkRef ∅

/-- Memo for the sealed enclosures of height-independent constants (`log π`, `(2π)⁻¹`, …), keyed
by a tag and the working precision; see `sealedConst`. -/
initialize sealedConstCache : IO.Ref (Std.HashMap (String × ℕ) RNear) ← IO.mkRef ∅

/-- Memo for the batch-shared error-bound enclosure: key `(sn, sd, D, withC₁)` of the batch's
lowest endpoint `sn/sd`; see `hardyErrOkSiteRS`. -/
initialize errBoundLoCacheRS : IO.Ref (Std.HashMap (ℕ × ℕ × ℕ × Bool) RNear) ← IO.mkRef ∅

end BSN
