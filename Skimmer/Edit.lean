/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

open Lean

structure Edit where
  range : Syntax.Range
  replacement : String
deriving Inhabited, BEq, Repr


instance : ToMessageData Syntax.Range where
  toMessageData range := m!"({range.start}:{range.stop})"


@[expose] def Lean.Syntax.Range.toSlice?  (s : String) (range : Syntax.Range) : Option String.Slice := do
  let startPos ← s.pos? range.start
  let endPos ← s.pos? range.start
  if h : startPos ≤ endPos then some ⟨s, startPos, endPos, h⟩ else none

deriving instance Repr for String.ValidPos

structure String.SliceOf (s : String) where
  /-- The byte position of the start of the string slice. -/
  startInclusive : s.ValidPos
  /-- The byte position of the end of the string slice. -/
  endExclusive : s.ValidPos
  /-- The slice is not degenerate (but it may be empty). -/
  startInclusive_le_endExclusive : startInclusive ≤ endExclusive

@[coe]
def String.SliceOf.toSlice {s} (sliceOf : String.SliceOf s) : Slice := { sliceOf with str := s }

def Lean.Syntax.Range.toSliceOf?  (s : String) (range : Syntax.Range) :
    Option (String.SliceOf s) := do
  let startPos ← s.pos? range.start
  let endPos ← s.pos? range.stop
  if h : startPos ≤ endPos then some ⟨startPos, endPos, h⟩ else none

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

theorem String.Pos.Raw.isValid_of_isUTF8FirstByte (s : String) (pos : Pos.Raw)
    (h_lt_end : pos < s.rawEndPos) (h : (s.getUTF8Byte pos h_lt_end).IsUTF8FirstByte) :
    pos.IsValid s :=
  pos.isValid_iff_isUTF8FirstByte.mpr (.inr ⟨_, h⟩)

theorem String.Pos.Raw.dec_le {p : String.Pos.Raw} : p.dec ≤ p := by simp [le_iff]

theorem String.Pos.Raw.lt_of_le_of_ne {p q : String.Pos.Raw} (h_le : p ≤ q) (h_ne : p ≠ q) :
    p < q := by
  obtain ⟨_⟩ := p; obtain ⟨_⟩ := q; simp at *; exact Nat.lt_of_le_of_ne h_le h_ne

theorem String.Pos.Raw.lt_of_not_le {p q : String.Pos.Raw} (h : ¬(p ≤ q)) : q < p := by
  obtain ⟨_⟩ := q; obtain ⟨_⟩ := p; simp_all

 /-- Gets the greatest `ValidPos` `v` of `s` such that `v ≤ p`. -/
@[expose, inline]
def String.Pos.Raw.floor' (s : String) (p : Pos.Raw) : { v : s.ValidPos // v.offset ≤ p } :=
  if h : p < s.rawEndPos then
    go p h (p.le_refl)
  else
    ⟨s.endValidPos, by -- can surely be golfed
      simp
      generalize s.rawEndPos = e at *
      obtain ⟨_⟩ := e; obtain ⟨_⟩ := p
      simp_all⟩
where
  go p' h (le : p' ≤ p) : { v : s.ValidPos // v.offset ≤ p } :=
    if isValid : (s.getUTF8Byte p' h).IsUTF8FirstByte then
      ⟨ValidPos.mk p' (p'.isValid_of_isUTF8FirstByte s h isValid), le⟩
    else
      have : sizeOf p'.dec < sizeOf p' := by
        by_cases atStart : p' = 0
        · grind [isUTF8FirstByte_getUTF8Byte_zero]
        · obtain ⟨byteIdx⟩ := p'
          simp at atStart; simp [dec]
          grind
      go p'.dec (String.Pos.Raw.lt_of_le_of_lt dec_le h) (Raw.le_trans dec_le le)

 /-- Gets the greatest `ValidPos` `v` of `s` such that `v ≤ p`. -/
def String.Pos.Raw.floor (s : String) (p : Pos.Raw) : s.ValidPos :=
  p.floor' s

theorem String.Pos.Raw.floor_le (s : String) (p : Pos.Raw) : (p.floor s).offset ≤ p := by
  simp only [floor]; grind

-- TODO: split into two functions, no `⊕`?
/-- Gets the least `ValidPos` `v` of `s` such that `p ≤ v`, if there is one. -/
@[expose, inline]
def String.Pos.Raw.ceiling' (s : String) (p : Pos.Raw) :
    { v : s.ValidPos // p ≤ v.offset } ⊕ { v : s.ValidPos // v = s.endValidPos ∧ s.rawEndPos < p} :=
  if h_p : p ≤ s.rawEndPos then
    .inl <| go h_p p h_p (p.le_refl)
  else
    .inr ⟨s.endValidPos, ⟨rfl, Raw.lt_of_not_le h_p⟩ ⟩
where
  go h_p p' h (le : p ≤ p') : { v : s.ValidPos // p ≤ v.offset } :=
    if atEnd : p' = s.rawEndPos then ⟨s.endValidPos, h_p⟩ else
      have h_lt := Raw.lt_of_le_of_ne h atEnd
      if isValid : (s.getUTF8Byte p' h_lt).IsUTF8FirstByte then
        ⟨ValidPos.mk p' (p'.isValid_of_isUTF8FirstByte s h_lt isValid), le⟩
      else
        have : s.rawEndPos.byteIdx - (p'.byteIdx + 1) < s.rawEndPos.byteIdx - p'.byteIdx := by
          clear isValid h_p
          generalize s.rawEndPos = e at *
          obtain ⟨_⟩ := e; obtain ⟨_⟩ := p'
          simp_all; grind
        go h_p p'.inc h_lt (Raw.le_of_lt <| Raw.lt_of_le_of_lt le lt_inc)
  termination_by s.rawEndPos.byteIdx - p'.byteIdx

/-- Gets the least `ValidPos` `v` of `s` such that `p ≤ v`, if there is one. -/
def String.Pos.Raw.ceiling? (s : String) (p : Pos.Raw) : Option s.ValidPos :=
  match p.ceiling' s with
  | .inl x => x.val
  | _ => none

/-- Gets the least `ValidPos` `v` of `s` such that `p ≤ v`, if there is one, or the end position. -/
def String.Pos.Raw.ceiling (s : String) (p : Pos.Raw) : s.ValidPos :=
  match p.ceiling' s with
  | .inl x | .inr x => x.val

theorem String.Pos.Raw.ceiling_le_or (s : String) (p : Pos.Raw) :
    p ≤ (p.ceiling s).offset ∨ (p.ceiling s = s.endValidPos ∧ s.rawEndPos < p) := by
  simp [ceiling]; grind

def String.Slice.length (s : String.Slice) : Nat := s.foldl (init := 0) fun count _ => count + 1

def String.Slice.isAtLeastLength (s : String.Slice) (n : Nat) : Bool :=
  go s.startPos n
where
  go (p : s.Pos) : Nat → Bool
    | 0 => true
    | n+1 => if h : p = s.endPos then false else go (p.next h) n

def String.Slice.isGreaterThanLength (s : String.Slice) (n : Nat) : Bool :=
  s.isAtLeastLength (n+1)

def String.Slice.summarizeLast (s : String.Slice) (n : Nat) : String :=
  if s.isGreaterThanLength n then "..." ++ s.takeEnd (n-3) else s.takeEnd n |>.copy

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

def String.Pos.Raw.cmp (p₁ p₂ : String.Pos.Raw) : Ordering :=
  compareOfLessAndBEq p₁ p₂

/-- Lexicographic order that first compares the start positions, then the end positions if there is a tie.-/
def Lean.Syntax.Range.cmp (r₁ r₂ : Syntax.Range) : Ordering :=
  r₁.start.cmp r₂.start |>.then <| r₁.stop.cmp r₂.stop

def Edit.cmp (e₁ e₂ : Edit) : Ordering :=
  e₁.range.cmp e₂.range

@[inline] def Array.sortEdits (edits : Array Edit) : Array Edit :=
  edits.qsort fun e₁ e₂ => e₁.cmp e₂ |>.isLT
