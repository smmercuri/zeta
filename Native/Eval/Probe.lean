module

/-!
# `Native.Eval.Probe`: is the compiled code loaded?

A plain loop for `Native.PluginCheck` to time: compiled, an iteration takes a few nanoseconds;
in the interpreter, over a hundred.
-/
@[expose] public section

namespace Native

/-- `n` steps of a scalar recurrence, whose result depends on every step. -/
def probeLoop (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    acc := (acc + i * 7) % 1000003
  return acc

end Native
