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

* `Sfrac`:the signed rational `sfrac` the enclosures are built from (the shared base);
* `Core`:the `IsNear` predicate, endpoints, signed-numerator parts, `const`, `widen`;
* `Arith`:`add`/`neg`/`sub`/`mul`, the literal-output combinators and their sign variants,
  `recentre`;
* `Images`:enclosures of `sin`/`cos`/`sqrt`/`inv` and the sandwich `of_interval`;
* `Verify`:the generic bound verifier, sign extraction, and the certificate comparisons;
* `Sums`:finite-sum splitting and transport.

The complex layer is `Enclosure.Complex` (imported separately, since it pulls in complex
`Mathlib`).
-/
@[expose] public section

