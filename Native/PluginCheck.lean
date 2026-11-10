/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Native.Eval.Probe

/-!
# Is `NativeEval` running as compiled code?

`native_decide` evaluates `Native.Eval` through the `NativeEval` library's compiled plugin when Lake
loads it, and through the much slower interpreter when it does not. Building this module fails
in the second case; in the first it prints nothing.
-/

-- Compiled, `probeLoop` runs well under the 30 ns-per-iteration threshold; interpreted, well over.
#eval show IO Unit from do
  let n := 10000000
  let t0 ← IO.monoNanosNow
  let r := Native.probeLoop (n + t0 % 1)
  -- use `r` before reading the clock again, so the loop cannot be moved past it
  if r == 1000003 then throw <| IO.userError "unreachable"
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / n.toFloat
  if ns > 30 then
    throw <| IO.userError s!"Native.Eval is not running compiled ({ns} ns/iteration): check in \
      lakefile.toml that `NativeEval` is precompiled, that its `libName` is its root module's \
      initializer stem, and that no other library's globs claim `Native.Eval` modules"
