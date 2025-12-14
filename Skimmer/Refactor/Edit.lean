/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean
public import Skimmer.Refactor.String

@[expose] public section

open Lean

structure Skimmer.Edit where
  range : Syntax.Range
  replacement : String
deriving Inhabited, BEq, Repr

open Skimmer

def String.Pos.Raw.cmp (p₁ p₂ : String.Pos.Raw) : Ordering :=
  compareOfLessAndBEq p₁ p₂

/-- Lexicographic order that first compares the start positions, then the end positions if there is a tie.-/
def Lean.Syntax.Range.cmp (r₁ r₂ : Syntax.Range) : Ordering :=
  r₁.start.cmp r₂.start |>.then <| r₁.stop.cmp r₂.stop

def Skimmer.Edit.cmp (e₁ e₂ : Edit) : Ordering :=
  e₁.range.cmp e₂.range

instance : Ord Edit where compare := Edit.cmp

/-- The extension holding all edits produced by any refactor. -/
-- TODO: we might also want to hold failures/errors/"uncertain edits" which need approval here.
initialize editExt : PersistentEnvExtension Edit (Array Edit) (Array Edit) ←
  registerPersistentEnvExtension {
    mkInitial := pure #[]
    addImportedFn := fun _ => pure #[]
    addEntryFn := Array.append
    statsFn edits := f!"{edits.size} edits"
    exportEntriesFnEx _ edits _ := edits.qsortOrd
  }

instance : ToMessageData Syntax.Range where
  toMessageData range := m!"({range.start}:{range.stop})"

/-- Assumes `edits` is sorted, and the ranges are disjoint. -/
def String.applyEdits (text : String) (edits : Array Edit) : String := Id.run do
  let mut out : String := ""
  let mut prevEndPos : text.ValidPos := text.startValidPos
  for edit in edits do -- note: already sorted
    let some slice := edit.range.toSliceOf? text | continue -- TODO: trace/error
    if h : prevEndPos ≤ slice.startInclusive then
      out := out ++ {
        str := text
        startInclusive := prevEndPos
        endExclusive := slice.startInclusive
        startInclusive_le_endExclusive := h : String.Slice }
      out := out ++ edit.replacement
      prevEndPos := slice.endExclusive
    -- TODO: trace/error if not
  out := out ++ text.replaceStart prevEndPos
  return out

/-- Assumes `edits` is sorted, and the ranges are disjoint. -/
def String.applyEditsWithTracing {m}
    [Monad m] [MonadTrace m] [MonadOptions m] [MonadRef m] [AddMessageContext m]
    (text : String) (edits : Array Edit) : m String := do
  let mut out : String := ""
  let mut prevEndPos : text.ValidPos := text.startValidPos
  let mut successCount := 0
  for edit in edits do -- note: already sorted
    let some slice := edit.range.toSliceOf? text
      | trace[Skimmer.Edit.Error] "💥{edit.range} Invalid positions"
        -- TODO: show enclosing string; handle past-the-end; handle ¬(start ≤ stop)
        continue
    trace[Skimmer.Edit] "{edit.range}\n- {repr slice.toSlice.copy}\n+ {repr edit.replacement}"
    if h : prevEndPos ≤ slice.startInclusive then
      out := out ++ {
        str := text
        startInclusive := prevEndPos
        endExclusive := slice.startInclusive
        startInclusive_le_endExclusive := h : String.Slice }
      out := out ++ edit.replacement
      prevEndPos := slice.endExclusive
      successCount := successCount + 1
    else
      trace[Skimmer.Edit.Error] "❌{edit.range} Overlaps with previous edit ending at \
        {prevEndPos.offset}\n\
        Summary of previous edit:\n\
        - {repr <| (text.replaceEnd prevEndPos).summarizeLast 10}\n\
        + {repr <| out.toSlice.summarizeLast 10}"
    -- TODO: trace/error if not
  out := out ++ text.replaceStart prevEndPos
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
  let mut prevEndPos := text.startValidPos
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
  out := out ++ text.replaceStart prevEndPos
  return out

instance : ToMessageData Edit where
  toMessageData e := m!"({e.range} ↦ \"{e.replacement}\")"
