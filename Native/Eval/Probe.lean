/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

/-!
# `Native.Eval.Probe`: is the compiled code loaded?

A plain loop that `Native.PluginCheck` times to tell compiled execution from interpreted.
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
