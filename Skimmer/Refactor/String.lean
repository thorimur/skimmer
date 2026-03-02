/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Syntax

/-! # Additional utilities for `String` -/

public section

structure String.SliceOf (s : String) where
  /-- The byte position of the start of the string slice. -/
  startInclusive : s.Pos
  /-- The byte position of the end of the string slice. -/
  endExclusive : s.Pos
  /-- The slice is not degenerate (but it may be empty). -/
  startInclusive_le_endExclusive : startInclusive ≤ endExclusive

@[expose] def Lean.Syntax.Range.toSlice?  (s : String) (range : Syntax.Range) : Option String.Slice := do
  let startPos ← s.pos? range.start
  let endPos ← s.pos? range.start
  if h : startPos ≤ endPos then some ⟨s, startPos, endPos, h⟩ else none

def Lean.Syntax.Range.toSliceOf?  (s : String) (range : Syntax.Range) :
    Option (String.SliceOf s) := do
  let startPos ← s.pos? range.start
  let endPos ← s.pos? range.stop
  if h : startPos ≤ endPos then some ⟨startPos, endPos, h⟩ else none

deriving instance Repr for String.Pos

namespace String

@[coe]
def SliceOf.toSlice {s} (sliceOf : SliceOf s) : Slice := { sliceOf with str := s }

theorem Pos.Raw.isValid_of_isUTF8FirstByte (s : String) (pos : Pos.Raw)
    (h_lt_end : pos < s.rawEndPos) (h : (s.getUTF8Byte pos h_lt_end).IsUTF8FirstByte) :
    pos.IsValid s :=
  pos.isValid_iff_isUTF8FirstByte.mpr (.inr ⟨_, h⟩)

theorem Pos.Raw.dec_le {p : Pos.Raw} : p.dec ≤ p := by simp [le_iff]

theorem Pos.Raw.lt_of_le_of_ne {p q : Pos.Raw} (h_le : p ≤ q) (h_ne : p ≠ q) :
    p < q := by
  obtain ⟨_⟩ := p; obtain ⟨_⟩ := q; simp at *; exact Nat.lt_of_le_of_ne h_le h_ne

theorem Pos.Raw.lt_of_not_le {p q : Pos.Raw} (h : ¬(p ≤ q)) : q < p := by
  obtain ⟨_⟩ := q; obtain ⟨_⟩ := p; simp_all

 /-- Gets the greatest `Pos` `v` of `s` such that `v ≤ p`. -/
@[expose, inline]
def Pos.Raw.floor' (s : String) (p : Pos.Raw) : { v : s.Pos // v.offset ≤ p } :=
  if h : p < s.rawEndPos then
    go p h (p.le_refl)
  else
    ⟨s.endPos, by -- can surely be golfed
      simp
      generalize s.rawEndPos = e at *
      obtain ⟨_⟩ := e; obtain ⟨_⟩ := p
      simp_all⟩
where
  go p' h (le : p' ≤ p) : { v : s.Pos // v.offset ≤ p } :=
    if isValid : (s.getUTF8Byte p' h).IsUTF8FirstByte then
      ⟨Pos.mk p' (p'.isValid_of_isUTF8FirstByte s h isValid), le⟩
    else
      have : sizeOf p'.dec < sizeOf p' := by
        by_cases atStart : p' = 0
        · grind [isUTF8FirstByte_getUTF8Byte_zero]
        · obtain ⟨byteIdx⟩ := p'
          simp at atStart; simp [dec]
          grind
      go p'.dec (Pos.Raw.lt_of_le_of_lt dec_le h) (Raw.le_trans dec_le le)

 /-- Gets the greatest `Pos` `v` of `s` such that `v ≤ p`. -/
def Pos.Raw.floor (s : String) (p : Pos.Raw) : s.Pos :=
  p.floor' s

theorem Pos.Raw.floor_le (s : String) (p : Pos.Raw) : (p.floor s).offset ≤ p := by
  simp only [floor]; grind

-- TODO: split into two functions, no `⊕`?
/-- Gets the least `Pos` `v` of `s` such that `p ≤ v`, if there is one. -/
@[expose, inline]
def Pos.Raw.ceiling' (s : String) (p : Pos.Raw) :
    { v : s.Pos // p ≤ v.offset } ⊕ { v : s.Pos // v = s.endPos ∧ s.rawEndPos < p} :=
  if h_p : p ≤ s.rawEndPos then
    .inl <| go h_p p h_p (p.le_refl)
  else
    .inr ⟨s.endPos, ⟨rfl, Raw.lt_of_not_le h_p⟩ ⟩
where
  go h_p p' h (le : p ≤ p') : { v : s.Pos // p ≤ v.offset } :=
    if atEnd : p' = s.rawEndPos then ⟨s.endPos, h_p⟩ else
      have h_lt := Raw.lt_of_le_of_ne h atEnd
      if isValid : (s.getUTF8Byte p' h_lt).IsUTF8FirstByte then
        ⟨Pos.mk p' (p'.isValid_of_isUTF8FirstByte s h_lt isValid), le⟩
      else
        have : s.rawEndPos.byteIdx - (p'.byteIdx + 1) < s.rawEndPos.byteIdx - p'.byteIdx := by
          clear isValid h_p
          generalize s.rawEndPos = e at *
          obtain ⟨_⟩ := e; obtain ⟨_⟩ := p'
          simp_all; grind
        go h_p p'.inc h_lt (Raw.le_of_lt <| Raw.lt_of_le_of_lt le lt_inc)
  termination_by s.rawEndPos.byteIdx - p'.byteIdx

/-- Gets the least `Pos` `v` of `s` such that `p ≤ v`, if there is one. -/
def Pos.Raw.ceiling? (s : String) (p : Pos.Raw) : Option s.Pos :=
  match p.ceiling' s with
  | .inl x => x.val
  | _ => none

/-- Gets the least `Pos` `v` of `s` such that `p ≤ v`, if there is one, or the end position. -/
def Pos.Raw.ceiling (s : String) (p : Pos.Raw) : s.Pos :=
  match p.ceiling' s with
  | .inl x | .inr x => x.val

theorem Pos.Raw.ceiling_le_or (s : String) (p : Pos.Raw) :
    p ≤ (p.ceiling s).offset ∨ (p.ceiling s = s.endPos ∧ s.rawEndPos < p) := by
  simp [ceiling]; grind

def Slice.isAtLeastLength (s : Slice) (n : Nat) : Bool :=
  go s.startPos n
where
  go (p : s.Pos) : Nat → Bool
    | 0 => true
    | n+1 => if h : p = s.endPos then false else go (p.next h) n

def Slice.isGreaterThanLength (s : Slice) (n : Nat) : Bool :=
  s.isAtLeastLength (n+1)

def Slice.summarizeLast (s : Slice) (n : Nat) : String :=
  if s.isGreaterThanLength n then "..." ++ s.takeEnd (n-3) else s.takeEnd n |>.copy

end String
