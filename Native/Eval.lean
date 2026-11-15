/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Native.Eval.Encl
public import Native.Eval.Const
public import Native.Eval.Log
public import Native.Eval.Arctan
public import Native.Eval.RiemannSiegel
public import Native.Eval.Batch
public import Native.Eval.Probe
public import Native.Eval.Store

/-!
# Native.Eval

The computable part of `Native`: every definition the native zero certificates evaluate. The
modules under `Native/Eval/` import no `Mathlib`, so their library (`NativeEval`) compiles to native
code (`precompileModules`) and `native_decide` runs the checks as machine code. The soundness
theorems, which use `Mathlib`, are in the rest of `Native`.
-/
