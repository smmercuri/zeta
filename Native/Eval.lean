module

public import Native.Eval.Encl
public import Native.Eval.Const
public import Native.Eval.Trig
public import Native.Eval.Log
public import Native.Eval.Arctan
public import Native.Eval.RiemannSiegel
public import Native.Eval.Batch
public import Native.Eval.Probe
public import Native.Eval.Store

/-!
# Native.Eval

The computable part of `Native`: every definition the native zero certificates evaluate, with no
`Mathlib` import, so that its library (`NativeEval`) compiles to native code (`precompileModules`)
and `native_decide` runs the checks as machine code rather than in the interpreter. The soundness
theorems, which do need `Mathlib`, are in the rest of `Native`. Nothing under `Native/Eval/` may
import `Mathlib`.
-/
