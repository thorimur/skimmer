/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Lean.Data.Array
import Skimmer.LinterWithCleanup.PunchCard

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

open Lean Elab Command

def Lean.Syntax.getRangeForRecordRange! (stx : Syntax) (isHeader := false) :
    CommandElabM String.Range := do
  let stop : String.Pos ← if stx.isOfKind ``Parser.Command.eoi then pure 0 else
    (stx.getTrailingTailPos? true).getDM <|
      panic! s!"`getCurrentRangeForRecordRange` called on non-canonical syntax {stx}"
  let start ← if isHeader then pure 0 else pure (← read).cmdPos
  return ⟨start, stop⟩

-- TODO: ++ `!` on both names

/-- Records the range of the given syntax in the `RangeBoundariesMod2` hashset at the index `idx` of `rangeRecordsRef`. If the result is a cycle (i.e. all syntax has been processed), punches the punchcard at the same index in `punchCardsRef`.

This should only be called on original syntax. -/
def IO.recordRange (idx : Nat) (range : String.Range) : BaseIO Unit := do
  let isCycle ← rangeRecordsRef.modifyGet fun a =>
    a.modifyGet idx fun rbs => let rbs := rbs.insertRange range; (rbs.isCycle, rbs)
  if isCycle then IO.punch! idx

def Lean.Elab.Command.recordRange (idx : Nat) (stx : Syntax) (isHeader := false) :
    CommandElabM Unit := do
  IO.recordRange idx <|← stx.getRangeForRecordRange! isHeader
