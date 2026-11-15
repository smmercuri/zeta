/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

/-!
# `Native.Eval.Store`: a batch's rows of the zero store

The lines `[lo, hi)` of a store file, found through an index of line starts built by one compiled
scan, so a batch decodes only its own rows and each file is read and indexed once per process.
Nothing here is trusted: a batch's statement fixes its count and ends, the rows are checked against
their index column, and `checkTiling` re-certifies whatever brackets they give.
-/
@[expose] public section

namespace Native

/-- The byte offsets at which the lines of `b` start, from offset `i` on, appended to `acc`. -/
partial def lineStartsFrom (b : ByteArray) (i : USize) (acc : Array USize) : Array USize :=
  if h : i.toNat < b.size then
    lineStartsFrom b (i + 1) (if b.uget i h == 10 then acc.push (i + 1) else acc)
  else acc

/-- The byte offset of every line start of `b`, and the end of `b` last. -/
def lineStarts (b : ByteArray) : Array USize :=
  (lineStartsFrom b 0 #[0]).push b.size.toUSize

/-- Lines `[lo, hi)` of `b`, as one string (empty if they are not valid UTF-8), given `b`'s
`lineStarts`. -/
def linesBetween (b : ByteArray) (starts : Array USize) (lo hi : Nat) : String :=
  let last := starts.size - 1
  let s := starts[min lo last]!
  let e := starts[min hi last]!
  (String.fromUTF8? (b.extract s.toNat e.toNat)).getD ""

end Native
