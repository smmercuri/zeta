import Native.Eval.Probe

/-!
# Is `NativeEval` running as compiled code?

`native_decide` evaluates `Native.Eval` through the `NativeEval` library's compiled plugin when Lake
loads it, and silently falls back to the interpreter, about 40 times slower, when it does not.
Building this module fails in the second case, so a native build cannot quietly run interpreted;
in the first it prints nothing.
-/

-- Compiled, `probeLoop` takes about 3 ns an iteration; interpreted, about 140 ns.
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
