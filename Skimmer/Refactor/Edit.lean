/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean
public import Skimmer.Refactor.String

public section

open Lean

/- TODO: need a better way to avoid overlapping edits. Ideally, we check at recording time;
we can check if the next position already recorded after the start of the new one is the "end" of some syntax range or if the one prior to the end is the "start" (and in either case fail).

RBMap? Maybe? I believe there's API for that kind of thing. (Could have two RBSets, or one RBMap to Bool.) Possibly the edits should be recorded in an RB thing anyway.

binary search in sorted array? No; means we're constantly resorting.

Possibly, we want to construct this at the end instead of `qsort`ing to avoid time spent in the ref.
-/

/- TODO: Edit subsets, and the ability to "imagine" how to shift edits after applying one subset. -/

deriving instance ToJson for String.Pos.Raw, Syntax.Range
deriving instance FromJson for String.Pos.Raw, Syntax.Range

structure Skimmer.Edit where
  range : Syntax.Range
  replacement : String
  /-- Holds an old version of the replacement that ought to be reviewed. -/
  shouldReview? : Option String := none -- Note: may be updated relative to the actual old source, if we do not need to review all of the edit.
  -- TODO: review functionality should be prior to the "raw" edits probably. Further, we need different review no-ops for different syntax categories, and possibly ways to expand to syntax which can be no-op'd. Would be good to have a monad that allowed this, and also allowed getting infotrees cheaply...
deriving Inhabited, BEq, Repr, Hashable, ToJson, FromJson

open Skimmer

def String.Pos.Raw.cmp (p₁ p₂ : String.Pos.Raw) : Ordering :=
  compareOfLessAndBEq p₁ p₂

/-- Lexicographic order that first compares the start positions, then the end positions if there is a tie.-/
def Lean.Syntax.Range.cmp (r₁ r₂ : Syntax.Range) : Ordering :=
  r₁.start.cmp r₂.start |>.then <| r₁.stop.cmp r₂.stop

def Skimmer.Edit.cmp (e₁ e₂ : Edit) : Ordering :=
  e₁.range.cmp e₂.range

instance : Ord Edit where compare := Edit.cmp

instance : ToMessageData Syntax.Range where
  toMessageData range := m!"({range.start}:{range.stop})"

instance : ToMessageData Edit where
  toMessageData e :=
    if let some old := e.shouldReview? then
      m!"[?](\"{old}\"@{e.range} ↦ \"{e.replacement}\")"
    else
      m!"({e.range} ↦ \"{e.replacement}\")"

/-- Assumes `edits` is sorted, and the ranges are disjoint. -/
def String.applyEdits (text : String) (edits : Array Edit) : String := Id.run do
  let mut out : String := ""
  let mut prevEndPos : text.Pos := text.startPos
  for edit in edits do -- note: already sorted
    let some replaced := edit.range.toSliceOf? text | continue -- TODO: trace/error
    if h : prevEndPos ≤ replaced.startInclusive then
      out := out ++ {
        str := text
        startInclusive := prevEndPos
        endExclusive := replaced.startInclusive
        startInclusive_le_endExclusive := h : String.Slice }
      if let some old := edit.shouldReview? then
        -- TODO: maybe this should be on the edit constructor side, especially for pretty-printing to the correct width and all. Consider this branch temporary.
        out := out ++ s!"review% ({old} => {edit.replacement})"
        -- TODO NOW: maybe log something?
      else
        out := out ++ edit.replacement
      prevEndPos := replaced.endExclusive
    -- TODO: trace/error if not
  out := out ++ text.sliceFrom prevEndPos
  return out

/-- Assumes `edits` is sorted, and the ranges are disjoint. -/
def String.applyEditsWithTracing {m}
    [Monad m] [MonadTrace m] [MonadOptions m] [MonadRef m] [AddMessageContext m]
    (text : String) (edits : Array Edit) : m String := do
  let mut out : String := ""
  let mut prevEndPos : text.Pos := text.startPos
  let mut successCount := 0
  for edit in edits do -- note: already sorted
    let some replaced := edit.range.toSliceOf? text
      | trace[Skimmer.Edit.Error] "💥{edit.range} Invalid positions"
        -- TODO: show enclosing string; handle past-the-end; handle ¬(start ≤ stop)
        continue
    trace[Skimmer.Edit] "{edit.range}\n- {repr replaced.toSlice.copy}\n+ {repr edit.replacement}"
    if h : prevEndPos ≤ replaced.startInclusive then
      out := out ++ {
        str := text
        startInclusive := prevEndPos
        endExclusive := replaced.startInclusive
        startInclusive_le_endExclusive := h : String.Slice }
      if let some old := edit.shouldReview? then
        -- TODO: maybe this should be on the edit constructor side, especially for pretty-printing to the correct width and all. Consider this branch temporary.
        out := out ++ s!"review% ({old} => {edit.replacement})"
        -- TODO NOW: maybe log something?
      else
        out := out ++ edit.replacement
      prevEndPos := replaced.endExclusive
      successCount := successCount + 1
    else
      trace[Skimmer.Edit.Error] "❌{edit.range} Overlaps with previous edit ending at \
        {prevEndPos.offset}\n\
        Summary of previous edit:\n\
        - {repr <| (text.sliceTo prevEndPos).summarizeLast 10}\n\
        + {repr <| out.toSlice.summarizeLast 10}"
    -- TODO: trace/error if not
  out := out ++ text.sliceFrom prevEndPos
  if successCount = edits.size then
    trace[Skimmer.Edit] "Successfully applied all {edits.size} \
      edit{if edits.size = 1 then "" else "s"}"
  else
    trace[Skimmer.Edit] "❗Failed to apply {edits.size - successCount} out of {edits.size} \
      edit{if edits.size - successCount = 1 then "" else "s"}\n\
      Successfully applied {successCount} out of {edits.size} \
      edit{if edits.size - successCount = 1 then "" else "s"}"
  return out

-- TODO: register traceclasses, inherit appropriately

/-! Testing function -/

/-- Brackets the ranges in `ranges`. Assumes the ranges are already sorted and are disjoint. -/
def String.bracketRanges (text : String) (ranges : Array Syntax.Range) : String := Id.run do
  let mut out : String := ""
  let mut prevEndPos := text.startPos
  for range in ranges do
    -- Technically, we don't need the slice, but usi
    let some slice := range.toSliceOf? text | continue
    if h : prevEndPos ≤ slice.startInclusive then
      -- append up to start of range
      out := out ++ {
        str := text
        startInclusive := prevEndPos
        endExclusive := slice.startInclusive
        startInclusive_le_endExclusive := h : String.Slice }
      out := out ++ "⟪"
      -- append range
      out := out ++ slice.toSlice
      out := out ++ "⟫"
      prevEndPos := slice.endExclusive
  out := out ++ text.sliceFrom prevEndPos
  return out
