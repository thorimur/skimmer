/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

open Lean

structure Edit where
  range : String.Range
  replacement : String
deriving Inhabited, BEq, Repr

/-- Assumes `edits` is sorted. -/
def String.applyEdits (text : String) (edits : Array Edit) : String := Id.run do
  -- Mario's code:
  let mut pos : String.Pos := 0
  let mut out : String := ""
  for edit in edits do -- already sorted
    if pos ≤ edit.range.start then
      out := out ++ text.extract pos edit.range.start ++ edit.replacement
      pos := edit.range.stop
  out := out ++ text.extract pos text.endPos
  return out

instance : ToMessageData Edit where
  toMessageData e := m!"([{e.range.start}:{e.range.stop}] ↦ \"{e.replacement}\")"

def String.Pos.cmp (p₁ p₂ : String.Pos) : Ordering :=
  compareOfLessAndBEq p₁ p₂

def String.Range.cmp (r₁ r₂ : String.Range) : Ordering :=
  r₁.start.cmp r₂.start |>.then <| r₁.stop.cmp r₂.stop

def Edit.cmp (e₁ e₂ : Edit) : Ordering :=
  e₁.range.cmp e₂.range

@[inline] def Array.sortEdits (edits : Array Edit) : Array Edit :=
  edits.qsort fun e₁ e₂ => e₁.cmp e₂ |>.isLT
