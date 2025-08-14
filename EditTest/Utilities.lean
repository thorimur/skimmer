import EditTest.Extension
import Lean
import Batteries

def Edit.delete (range : String.Range) : Edit where
  range
  replacement := ""

-- In future: need to account for things like code fencing. Should maybe detect by lack of good punctiation at end?
def removeBadNewlines (s : String) (stop : String.Pos := s.endPos) : List Edit := Id.run <| do
  let mut i : String.Pos := 0
  let mut numConsecNewlines := 0
  let mut startConsecNewline : String.Pos := 0
  let mut mostRecentNewline : String.Pos := 0
  let mut edits : List Edit := []
  while i < stop do
    let c := s.get i
    if c == '\n' then
      if numConsecNewlines == 0 then
        startConsecNewline := i
      mostRecentNewline := i
      numConsecNewlines := numConsecNewlines + 1
    else if !c.isWhitespace then
      if !c.isUpper then
        if numConsecNewlines > 1 then
          edits := {
              range := { start := startConsecNewline, stop := mostRecentNewline },
              replacement := ""
            } :: edits
      else
        if numConsecNewlines > 2 then
          edits := {
              range := { start := startConsecNewline, stop := mostRecentNewline },
              replacement := "\n"
            } :: edits
      numConsecNewlines := 0
    i := s.next i
  if numConsecNewlines > 1 then
    edits := {
        range := { start := startConsecNewline, stop := mostRecentNewline },
        replacement := ""
      } :: edits
  return edits.reverse

open Lean Parser Command Syntax

instance : HAdd (String.Range) (String.Pos) (String.Range) where
  hAdd := fun range offset => ⟨range.1 + offset, range.2 + offset⟩

def Edit.shiftEdit (e : Edit) (offset : String.Pos) : Edit :=
  { e with range := e.range + offset }

deriving instance Repr for FileMap

instance : Ord Lean.Position where
  compare p₁ p₂ := compare p₁.line p₂.line |>.then <| compare p₁.column p₂.column

open String in
@[inline] def String.matchAtMostNAux (s : String) (p : Char → Bool) (stopPos : String.Pos)
    (max : Nat) (pos : Pos) : Nat × Pos :=
  if 0 < max then
    if pos < stopPos then
      if p (s.get pos) then
        s.matchAtMostNAux p stopPos (max - 1) (s.next pos)
      else
        (max, pos)
    else if pos = stopPos then
      (max, pos)
    else
      (max + 1, stopPos)
  else (max, pos)

open String in
@[inline] def String.matchBeforeAux (s : String) (p : Char → Bool) (stopPos : Pos)
    (count : Nat) (pos : Pos) : Nat × Pos :=
  if h : pos < stopPos then
    if p (s.get pos) then
      have := Nat.sub_lt_sub_left h (lt_next s pos)
      s.matchBeforeAux p stopPos (count + 1) (s.next pos)
    else
      (count, pos)
  else if pos = stopPos then
    (count, pos)
  else (count - 1, stopPos)
termination_by stopPos.1 - pos.1

def String.matchAtMostN (s : String) (p : Char → Bool) (max : Nat) (startPos : Pos := 0)
    (stopPos : String.Pos := s.endPos) : Pos :=
  (s.matchAtMostNAux p stopPos max startPos).2

def String.matchN? (s : String) (p : Char → Bool) (n : Nat) (startPos : Pos := 0) (stopPos : Pos := s.endPos) :
    Option String.Pos :=
  if n = 0 then
    startPos
  else
    let (remaining, pos) := s.matchAtMostNAux p stopPos n startPos
    if remaining = 0 then some pos else none

def String.match (s : String) (p : Char → Bool) (startPos : Pos := 0) (stopPos : Pos := s.endPos) :
    Nat × String.Pos :=
  s.matchBeforeAux p stopPos 0 startPos

def String.findFromUntil? (s : String) (p : Char → Bool)
    (startPos : String.Pos := 0) (stopPos : String.Pos := s.endPos) : Option String.Pos := Id.run do
  let i := findAux s p stopPos startPos
  if i >= stopPos then return none else return i

def String.findNontrivialStartOfLine? (s : String)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option String.Pos := do
  let l ← s.findFromUntil? (· = '\n') startPos stopPos
  return (s.match (· = '\n') l stopPos).2

/-- The first indent after the first (consecutive sequence of) newline(s), given in the form
(numberOfSpaces, ⟨start, stop⟩). -/
def String.findExtraSpaceIndentBySecondLine? (s : String)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option (Nat × String.Range) := do
  let l ← s.findNontrivialStartOfLine? startPos stopPos
  let (count, i) ← s.match (· = ' ') l stopPos
  return (count, ⟨l, i⟩)

def String.dedents? (s : String) (indent : Nat := 0)
    (startPos : String.Pos := 0) (stopPos := s.endPos) : Option (Array Edit) := do
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

def Lean.FileMap.dedents? (map : FileMap) (r : String.Range) (customIndent? : Option Nat := none)
    (dedentFirstLine := false) : Option (Array Edit) := do
  let indent := customIndent?.getD <|
    let (_, indent, endPos) := getFirstLineIndent map r
    if endPos = r.start then indent else 0
  let firstDedent? := if dedentFirstLine then
      let (lineStart, actualIndent, endPos) := getFirstLineIndent map r
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
where
  getFirstLineIndent (map : FileMap) (r : String.Range) : String.Pos × Nat × String.Pos :=
    let lineStart := map.lineStart (map.toPosition r.start).line
    (lineStart, map.source.match (· = ' ') (startPos := lineStart) (stopPos := r.start))

def Lean.FileMap.getLineContents (map : FileMap) (line : Nat) (lastLine := line) : String :=
  map.source.extract (map.lineStart line) (map.lineStart (lastLine + 1))

def Lean.FileMap.getLines (map : FileMap) (range : String.Range) : Nat × Nat :=
  ((map.toPosition range.start).line, (map.toPosition range.stop).line)

elab "#test" doc:docComment : command => do
  if let some range := doc.raw.getRange? then
    let map ← getFileMap
    let (firstLine, lastLine) := map.getLines range
    let some edits := map.dedents? range (some 0) true | logWarning "No edits"
    logInfo m!"{edits}"
    -- let i := map.source.findExtraSpaceIndentBySecondLine? range.1 range.2
    let some i := map.source.findNontrivialStartOfLine? range.1 range.2 | throwError "no start"
    logInfo m!"i: \"{repr <| map.source.get i}\" @{i}"
    logInfo m!"i: \"{repr <| map.source.extract (i - ⟨2⟩) (i + ⟨2⟩)}\""
    let j := map.source.match (· = ' ') i range.2
    logInfo m!"j: {j.1} {repr <| map.source.get j.2}@{j} {j.2} ~ {range.2} {decide <| j.2 < range.2}"
    let poses := Id.run do
      let mut a := #[]
      let mut pos := range.2
      for _ in [:5] do
        a := a.push pos
        pos := map.source.next pos
      pure a
    logInfo m!"poses := {poses}"
    let newMap := (map.source.applyEdits edits.sortEdits).toFileMap
    logInfo m!"{newMap.getLineContents firstLine lastLine}"


#test
      /-- The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that
          `g` is injective on `s ∩ support (f ∘ g)`. -/


-- /-- Treats `s` as a single line (assuming that the newline is at the end) and so only dedents the first line. Does not check that `s` is a single line. -/
-- def String.dedentLineEdit (s : String) (limit : Option String.Pos := none) : Option Edit := Id.run do
--   let i := s.find fun c => !(c = ' ' || c = '\t')
--   if i = 0 then
--     return none
--   else if let some lim := limit then
--     return some (.delete ⟨0, min i lim⟩)
--   else
--     return some (.delete ⟨0, i⟩)




#eval Id.run do
  let s := "  argawg\n\n  brgaerg\n\n\n    gaerg. \n-/"
  let some edits := s.dedents? 1 | return "oops"
  applyEdits s edits
  /-
    4

    5
  -/
elab "#show_filemap" : command => do
  let map ← getFileMap
  -- logInfo m!"{map.positions}"
  let line := 107
  let lineEnd := 112
  let r : String.Range := ⟨map.lineStart line + ⟨2⟩, map.lineStart lineEnd⟩
  let lineStart := map.lineStart (map.toPosition r.start).line
  let precededBy := map.source.extract lineStart r.start
  let indent := if precededBy.all (· = ' ') then precededBy.endPos else 0
  logInfo m!"{repr <| "(" ++ map.source.extract r.1 r.2 ++ ")"}"
  logInfo m!"{indent}"


elab "#show_doc " doc:docComment : command => do
  -- logInfo m!"\"{repr <| doc.raw.getArg 1}\""
  let edit :: _ := let val := doc.raw[1].getAtomVal; removeBadNewlines val (stop := val.endPos - ⟨2⟩) | throwError "empty"
  logInfo m!"edit: {repr edit}}"
  logInfo m!"extracted:\n\"{doc.raw[1].getAtomVal.extract edit.range.1 edit.range.2}\""
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
