/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Native.Eval.Const
public import Native.Encl
public import Enclosure.BinarySplit.Tactic.Pi
public import Enclosure.BinarySplit.Tactic.Log2

/-!
# Native constants: `π` and `log 2`

Enclosures of `π` and `log 2` to `1/10⁵⁰`, with the fields of the kernel-checked constants
`BSN.pi_near_50` and `BSN.log2_near_50`.
-/
@[expose] public section

namespace Native

open Enclosure BSN

theorem piEncl_encloses : piEncl.Encloses Real.pi := pi_near_50

theorem log2Encl_encloses : log2Encl.Encloses (Real.log 2) := log2_near_50

end Native
