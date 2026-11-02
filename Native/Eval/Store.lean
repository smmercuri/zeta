module

/-!
# `Native.Eval.Store`: a batch's rows of the zero store

The lines `[lo, hi)` of a store file, found through an index of line starts built by one compiled
scan, so a batch decodes and splits only its own rows rather than the whole store file
(250,000 rows, ~9 MB), and each file is read and indexed once per process rather than once per
batch.
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
