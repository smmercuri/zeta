/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Enclosure.Core
public import Enclosure.Arith
public import Enclosure.Images
public import Enclosure.Verify
public import Enclosure.Sums

/-!
# Real interval enclosures

Umbrella for the real `Real.IsNear` interval-arithmetic layer (namespace `Enclosure`). The concerns
live in `Enclosure.*`:

* `Sfrac`: the signed rational `sfrac` the enclosures are built from (the base);
* `Core`: the `IsNear` predicate, endpoints, signed-numerator parts, `const`, `widen`;
* `Arith`: `add`/`neg`/`sub`/`mul`, the literal-output combinators and their sign variants,
  `recentre`;
* `Images`: enclosures of `sin`/`cos`/`sqrt`/`inv` and the sandwich `of_interval`;
* `Verify`: the generic bound verifier, sign extraction, and the certificate comparisons;
* `Sums`: finite-sum splitting and transport.

The complex layer `Enclosure.Complex` is imported separately, since it pulls in complex
`Mathlib`.
-/
@[expose] public section

