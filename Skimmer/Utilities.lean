/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Extension
import Lean
import Batteries

open Lean

def Edit.delete (range : Syntax.Range) : Edit where
  range
  replacement := ""

theorem String.ValidPos.le_endValidPos {s : String} (i : s.ValidPos) : i ≤ s.endValidPos :=
  i.isValid.le_rawEndPos

theorem String.ValidPos.ne_endValidPos_of_lt {s : String} {i j : s.ValidPos} (h : i < j) :
    i ≠ s.endValidPos := by
  have := j.le_endValidPos
  simp [lt_iff, le_iff, String.ValidPos.ext_iff,
    String.Pos.Raw.lt_iff, String.Pos.Raw.le_iff, String.Pos.Raw.ext_iff] at *
  grind only

-- In future: need to account for things like code fencing. Should maybe detect by lack of good punctiation at end?
def removeBadNewlines (s : String) (stop : s.ValidPos := s.endValidPos) : Array Edit := Id.run <| do
  let mut i : s.ValidPos := s.startValidPos
  let mut numConsecNewlines := 0
  let mut startConsecNewline : s.ValidPos := s.startValidPos
  let mut mostRecentNewline : s.ValidPos := s.startValidPos
  let mut edits : Array Edit := #[]
  while h : i < stop do
    let c := i.get (String.ValidPos.ne_endValidPos_of_lt h)
    -- TODO: move to after when possible...
    let next := i.next (String.ValidPos.ne_endValidPos_of_lt h)
    -- pure ()
    if true then pure () else pure ()
    if c == '\n' then
      if numConsecNewlines == 0 then startConsecNewline := i
      mostRecentNewline := i
      numConsecNewlines := numConsecNewlines + 1
    else if !c.isWhitespace then
      if !c.isUpper then
        if numConsecNewlines > 1 then
          edits := edits.push <| .delete
            { start := startConsecNewline.offset, stop := mostRecentNewline.offset }
      else
        if numConsecNewlines > 2 then
          edits := edits.push {
              range := { start := startConsecNewline.offset, stop := mostRecentNewline.offset },
              replacement := "\n"
            }
      numConsecNewlines := 0
    i := next
  if numConsecNewlines > 1 then
    edits := edits.push <| .delete
      { start := startConsecNewline.offset, stop := mostRecentNewline.offset }
  return edits

open Lean Parser Command Syntax

-- TODO: reconsider

instance : Add String.Pos.Raw where
  add := fun ⟨byteIdx₁⟩ ⟨byteIdx₂⟩ => ⟨byteIdx₁ + byteIdx₂⟩

instance : Sub String.Pos.Raw where
  sub := fun ⟨byteIdx₁⟩ ⟨byteIdx₂⟩ => ⟨byteIdx₁ - byteIdx₂⟩

instance : HAdd Syntax.Range String.Pos.Raw Syntax.Range where
  hAdd := fun range offset => ⟨range.1 + offset, range.2 + offset⟩

def Edit.shiftEdit (e : Edit) (offset : String.Pos.Raw) : Edit :=
  { e with range := e.range + offset }

deriving instance Repr for FileMap

instance : Ord Lean.Position where
  compare p₁ p₂ := compare p₁.line p₂.line |>.then <| compare p₁.column p₂.column

namespace String

/-! TODO: update to `ValidPos` -/

open String in
@[inline] def matchAtMostNAux (s : String) (p : Char → Bool) (stopPos : String.Pos.Raw)
    (max : Nat) (pos : Pos.Raw) : Nat × Pos.Raw :=
  if 0 < max then
    if pos < stopPos then
      if p (pos.get s) then
        s.matchAtMostNAux p stopPos (max - 1) (pos.next s)
      else
        (max, pos)
    else if pos = stopPos then
      (max, pos)
    else
      (max + 1, stopPos)
  else (max, pos)

open String in
@[inline] def matchBeforeAux (s : String) (p : Char → Bool) (stopPos : Pos.Raw)
    (count : Nat) (pos : Pos.Raw) : Nat × Pos.Raw :=
  if h : pos < stopPos then
    if p (pos.get s) then
      have := Nat.sub_lt_sub_left h (pos.byteIdx_lt_byteIdx_next s)
      s.matchBeforeAux p stopPos (count + 1) (pos.next s)
    else
      (count, pos)
  else if pos = stopPos then
    (count, pos)
  else (count - 1, stopPos)
termination_by stopPos.1 - pos.1

def matchAtMostN (s : String) (p : Char → Bool) (max : Nat) (startPos : Pos.Raw := 0)
    (stopPos : String.Pos.Raw := s.rawEndPos) : Pos.Raw :=
  (s.matchAtMostNAux p stopPos max startPos).2

def matchN? (s : String) (p : Char → Bool) (n : Nat) (startPos : Pos.Raw := 0) (stopPos : Pos.Raw := s.rawEndPos) :
    Option String.Pos.Raw :=
  if n = 0 then
    startPos
  else
    let (remaining, pos) := s.matchAtMostNAux p stopPos n startPos
    if remaining = 0 then some pos else none

def «match» (s : String) (p : Char → Bool) (startPos : Pos.Raw := 0) (stopPos : Pos.Raw := s.rawEndPos) :
    Nat × String.Pos.Raw :=
  s.matchBeforeAux p stopPos 0 startPos

def findFromUntil? (s : String) (p : Char → Bool)
    (startPos : String.Pos.Raw := 0) (stopPos : String.Pos.Raw := s.rawEndPos) : Option String.Pos.Raw := Id.run do
  let i := findAux s p stopPos startPos
  if i >= stopPos then return none else return i

def findNontrivialStartOfLine? (s : String)
    (startPos : String.Pos.Raw := 0) (stopPos := s.rawEndPos) : Option String.Pos.Raw := do
  let l ← s.findFromUntil? (· = '\n') startPos stopPos
  return (s.match (· = '\n') l stopPos).2

/-- The first indent after the first (consecutive sequence of) newline(s), given in the form
(numberOfSpaces, ⟨start, stop⟩). -/
def findExtraSpaceIndentBySecondLine? (s : String)
    (startPos : String.Pos.Raw := 0) (stopPos := s.rawEndPos) : Option (Nat × Syntax.Range) := do
  let l ← s.findNontrivialStartOfLine? startPos stopPos
  let (count, i) ← s.match (· = ' ') l stopPos
  return (count, ⟨l, i⟩)

def dedents? (s : String) (indent : Nat := 0)
    (startPos : String.Pos.Raw := 0) (stopPos : String.Pos.Raw := 0) :
    Option (Array Edit) := do
  let (extraIndent, ir) ← s.findExtraSpaceIndentBySecondLine? startPos stopPos
  let dedent := extraIndent - indent
  guard <| 0 < dedent
  let mut i := ir.start
  let mut edits : Array Edit := #[]
  while i < stopPos do
    let some j₀ := s.matchN? (· = ' ') indent (startPos := i) (stopPos := stopPos) | break
    let j₁ := s.matchAtMostN (· = ' ') dedent (startPos := j₀) (stopPos := stopPos)
    if j₀ < j₁ then
      edits := edits.push <| .delete { start := j₀, stop := j₁ }
    let some j₁ := s.findNontrivialStartOfLine? j₁ stopPos | break
    i := j₁
  if edits.isEmpty then none else return edits

end String

namespace Lean.FileMap

@[inline] def lineStartOfPos (map : FileMap) (pos : String.Pos.Raw) : String.Pos.Raw :=
  map.lineStart (map.toPosition pos).line

-- TODO: check that this works as expected at eof
/-- Gives the position of the start of the next line. -/
@[inline] def lineEndOfPos (map : FileMap) (pos : String.Pos.Raw) : String.Pos.Raw :=
  map.lineStart ((map.toPosition pos).line + 1)

/-- Returns `(lineStart, numSpaces, stopIndent)`. Note that `stopIndent` may be earlier than `pos`, but is not later. Only considers spaces to be indent characters (not tabs). -/
def getIndentBefore (map : FileMap) (pos : String.Pos.Raw) : String.Pos.Raw × Nat × String.Pos.Raw :=
  let lineStart := map.lineStartOfPos pos
  (lineStart, map.source.match (· = ' ') (startPos := lineStart) (stopPos := pos))

def getIndentTo? (map : FileMap) (pos : String.Pos.Raw) : Option (String.Pos.Raw × Nat) :=
  let (lineStart, indent, endPos) := map.getIndentBefore pos
  if pos = endPos then some (lineStart, indent) else none

def dedents? (map : FileMap) (r : Syntax.Range) (customIndent? : Option Nat := none)
    (dedentFirstLine := false) : Option (Array Edit) := do
  -- structure this code better, esp. `indent` and `firstDedent?`
  let indent := customIndent?.getD <|
    let (_, indent, endPos) := map.getIndentBefore r.start
    if endPos = r.start then indent else 0
  let firstDedent? := if dedentFirstLine then
      let (lineStart, actualIndent, endPos) := map.getIndentBefore r.start
      let indent := customIndent?.getD 0
      if indent < actualIndent then
        some (Edit.delete { start := lineStart + ⟨indent⟩, stop := endPos })
      else
        none
    else none
  match firstDedent?, map.source.dedents? indent r.start r.stop with
  | none, a => a
  | some edit, some edits => some (edits.push edit) -- will be sorted by the extension
  | some edit, none => some #[edit]

def getLineContents (map : FileMap) (line : Nat) (lastLine := line) : String :=
  (map.lineStart line).extract map.source (map.lineStart (lastLine + 1))

def getLines (map : FileMap) (range : Syntax.Range) : Nat × Nat :=
  ((map.toPosition range.start).line, (map.toPosition range.stop).line)

end Lean.FileMap

elab "#test" doc:docComment : command => do
  if let some range := doc.raw.getRange? then
    let map ← getFileMap
    let (firstLine, lastLine) := map.getLines range
    let some edits := map.dedents? range (some 0) true | logWarning "No edits"
    logInfo m!"{edits}"
    -- let i := map.source.findExtraSpaceIndentBySecondLine? range.1 range.2
    let some i := map.source.findNontrivialStartOfLine? range.1 range.2 | throwError "no start"
    logInfo m!"i: \"{repr <| i.get map.source}\" @{i}"
    let j := map.source.match (· = ' ') i range.2
    logInfo m!"j: \
      {j.1} {repr <| j.2.get map.source}@{j} {j.2} ~ {range.2} {decide <| j.2 < range.2}"
    let poses := Id.run do
      let mut a := #[]
      let mut pos := range.2
      for _ in [:5] do
        a := a.push pos
        pos := pos.next map.source
      pure a
    logInfo m!"poses := {poses}"
    let newMap := (map.source.applyEdits edits.sortEdits).toFileMap
    logInfo m!"{newMap.getLineContents firstLine lastLine}"


-- #test
      -- /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
      --     `g` is injective on `s ∩ support (f ∘ g)`. -/


-- /-- Treats `s` as a single line (assuming that the newline is at the end) and so only dedents the first line. Does not check that `s` is a single line. -/
-- def String.dedentLineEdit (s : String) (limit : Option String.Pos := none) : Option Edit := Id.run do
--   let i := s.find fun c => !(c = ' ' || c = '\t')
--   if i = 0 then
--     return none
--   else if let some lim := limit then
--     return some (.delete ⟨0, min i lim⟩)
--   else
--     return some (.delete ⟨0, i⟩)




-- #eval Id.run do
--   let s := "  argawg\n\n  brgaerg\n\n\n    gaerg. \n-/"
--   let some edits := s.dedents? 1 | return "oops"
--   applyEdits s edits
  /-
    4

    5
  -/
elab "#show_filemap" : command => do
  let map ← getFileMap
  -- logInfo m!"{map.positions}"
  let line := 107
  let lineEnd := 112
  let r : Syntax.Range := ⟨map.lineStart line + ⟨2⟩, map.lineStart lineEnd⟩
  let lineStart := map.lineStart (map.toPosition r.start).line
  let precededBy := lineStart.extract map.source r.start
  let indent := if precededBy.all (· = ' ') then precededBy.rawEndPos else 0
  logInfo m!"{repr <| "(" ++ r.1.extract map.source r.2 ++ ")"}"
  logInfo m!"{indent}"


elab "#show_doc " doc:docComment : command => do
  -- logInfo m!"\"{repr <| doc.raw.getArg 1}\""
  let val := doc.raw[1].getAtomVal
  let some stop := val.endValidPos.prev? |>.bind (·.prev?)
    | throwError "Couldn't move back 2 characters from the end."
  let edits := removeBadNewlines val (stop := stop)
  let some edit := edits[0]? | throwError "empty"
  logInfo m!"edit: {repr edit}}"
  logInfo m!"extracted:\n\"{edit.range.1.extract doc.raw[1].getAtomVal  edit.range.2}\""
  logInfo m!"\"{repr doc.raw[1]}\""

-- #print getDocStringText

-- #print String.


/-
def test := "a

  `D


  c"
#eval Id.run do
  let edit :: _ := removeBadNewlines test | return "empty"
  test.extract edit.range.start edit.range.stop
-/
