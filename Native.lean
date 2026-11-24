module

public import Native.Encl
public import Native.Const
public import Native.Log
public import Native.Arctan
public import Native.Fix
public import Native.RiemannSiegel
public import Native.Batch

/-!
# Native

The zero certificates checked by compiled evaluation (`native_decide`) rather than by the kernel.
A computable checker computes each enclosure's fields and checks the `Bool` side conditions of the
`Enclosure` lemma it mirrors; a soundness theorem turns a `true` result into the `BatchSpec` the
kernel-checked proof builds. The resulting theorems also trust the Lean compiler
(`Lean.ofReduceBool`).

The checker's definitions are in `Native.Eval` (library `NativeEval`, free of `Mathlib` and
compiled to native code); the modules here prove them sound:

* `Native.Encl`: enclosure fields as data, with exact arithmetic, recentring, reciprocal and square
  root;
* `Native.Const`: `π` and `log 2` to `1/10⁵⁰`;
* `Native.Log`: `log` of rationals, naturals and positive enclosures, reducing by `2ᵏ`;
* `Native.Arctan`: `arctan` of a rational below `1`;
* `Native.Fix`: fixed-point enclosures, and `cos`/`sin` through a table at multiples of `1/128`;
* `Native.RiemannSiegel`: the linear-free and full Riemann–Siegel approximants and their error
  bounds at a rational endpoint;
* `Native.Batch`: a batch's check over its boundaries, and `batchSpec_of_tiling`, which turns it
  into the `BatchSpec` a kernel-checked batch exports;
* `Native.BuildCerts`: `build_batch_rs +native lo hi`, the native counterpart of `build_batch_rs`,
  closing a batch's `BatchSpec` from the store rows by `native_decide` on that check.

The generated `Native.Certificates` (from `python/src/data_gen/gen_native_certificates.py`),
`Native.CountCertificates` and `Native.Main` assemble these into
`Native.riemannHypothesisUpTo_10011`; `scripts/build.sh --native` builds it.
-/
