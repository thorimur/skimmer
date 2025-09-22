import EditTest.Lean.Data.Array
import EditTest.AccumulativeLinter.PunchCard

abbrev RangeBoundariesMod2 := Std.HashSet String.Pos

namespace RangeBoundariesMod2

def insertMod2 (m : RangeBoundariesMod2) (k : String.Pos) : RangeBoundariesMod2 :=
  if m.contains k then m.erase k else m.insert k

def insertRange (m : RangeBoundariesMod2) (r : String.Range) : RangeBoundariesMod2 :=
  m.insertMod2 r.start |>.insertMod2 r.stop

def isRange (m : RangeBoundariesMod2) (start stop : String.Pos) : Bool :=
  m.size = 2 && m.contains start && m.contains stop

@[inline] def isCycle (m : RangeBoundariesMod2) : Bool :=
  m.size = 0

end RangeBoundariesMod2

-- TODO: consider switching to `Name`-indexed structure instead of `Array`?
/-- This should only be pushed to by `addLinterWithCleanup`. -/
initialize rangeRecordsRef : IO.Ref (Array RangeBoundariesMod2) ← IO.mkRef #[]

open Lean

private def _root_.Lean.Syntax.getRangeWithTrailingAndLoopOnEOI? (stx : Syntax) :
    Option String.Range :=
  if stx.getKind == ``Parser.Command.eoi then
    -- Currently, `getRangeWithTrailing?` returns `⟨pos, 0⟩` for `eoi`, but this may change.
    stx.getRangeWithTrailing? (canonicalOnly := true) |>.map fun r =>
      if r.stop == 0 then r else ⟨r.start, 0⟩
  else
    stx.getRangeWithTrailing? (canonicalOnly := true)

/-- Records the range of the given syntax in the `RangeBoundariesMod2` hashset at the index `idx` of `rangeRecordsRef`. If the result is a cycle (i.e. all syntax has been processed), punches the punchcard at the same index in `punchCardsRef`.

This should only be called on original syntax. -/
def IO.recordRange (idx : Nat) (stx : Syntax) : BaseIO Unit := do
  let some range := stx.getRangeWithTrailingAndLoopOnEOI?
    | panic! "`IO.recordRange` called on noncanonical syntax"
  let isCycle ← rangeRecordsRef.modifyGet fun a =>
    a.modifyGet idx fun rbs => let rbs := rbs.insertRange range; (rbs.isCycle, rbs)
  if isCycle then IO.punch! idx
