import Lean
import Batteries

open Lean Elab Command

/-!
# Version-tied data

-/


/-- The index for `StatefulLinter` states of the form `SourceIndexed α`.

The `BEq` instance compares only the `line`, so that we are more likely to destroy stale state.

The `hash` ought to be the hash of the file up through the end of the command syntax, so that we can detect if a linter's output is invalid. Note that technically a linter could determine its persistent data by looking at aspects of the environment which are sensitive to concurrency, and so edits below the source syntax might still invaldiate the state. Such linters should hash the entire source. -/
-- Note: could include `hashWholeFile` as a type parameter?
structure VersionedLine (hashWholeFile : Bool) where
  /-- The line on which the relevant command syntax starts. -/
  line : Nat
  /-- The hash of the source that we want to make sure does not change. -/
  hash : UInt64

/- Can change every `map` to something that works in a `MonadFileMap` monad... -/

-- Does this do anything?
attribute [specialize hashWholeFile] VersionedLine.mk VersionedLine.line VersionedLine.hash

/-- Only compares by line. -/
@[specialize b] instance VersionedLine.instBEqByLine {b} : BEq (VersionedLine b) where
  beq := (·.line == ·.line)

/-- Only compares by line. -/
@[specialize b] instance VersionedLine.instOrdByLine {b} : Ord (VersionedLine b) where
  compare := (compare ·.line ·.line)

/-- Only hashes the `line` (and does not really hash at all, but just represents it as a `UInt64`,
as does the standard `Hashable` instance for `Nat`) -/
@[specialize b] instance VersionedLine.instHashableByLine {b} : Hashable (VersionedLine b) where
  hash v := UInt64.ofNat v.line

@[inline] def String.hashRange (s : String) (range : String.Range) : UInt64 :=
  (s.extract range.start range.stop).hash

@[specialize hashWholeFile] def String.Range.toVersionedLine (range : String.Range) (map : FileMap) {hashWholeFile} :
    VersionedLine hashWholeFile where
  line := (map.toPosition range.start).line
  hash := if hashWholeFile then map.source.hash else map.source.hashRange ⟨0, range.stop⟩

def VersionedLine.isValid (v : VersionedLine false) (range : String.Range) (map : FileMap) :
    Bool :=
  v.hash = map.source.hashRange ⟨0, range.stop⟩

def VersionedLine.isValidWholeFile (v : VersionedLine true) (map : FileMap) :
    Bool :=
  v.hash = map.source.hash

@[inline, specialize hashWholeFile] def VersionedLine.isValidP {hashWholeFile}
    (v : VersionedLine hashWholeFile) (range : String.Range) (map : FileMap) : Bool :=
  if h : hashWholeFile then
    (h ▸ v).isValidWholeFile map
  else
    (eq_false_of_ne_true h ▸ v).isValid range map

/- We choose `PersistentHashMap`s because they are extensible and shareable. However, the number of entries is bounded by the number of lines in the file, and the hash of a natural number is the number itself. As such, a simple `List` might be okay. -/

/-- Data of type `α` indexed by a line in the source file. -/
def SourceIndexed (α) (hashWholeFile := false) := PersistentHashMap (VersionedLine hashWholeFile) α

def SourceIndexedList (α) (hashWholeFile := false) := List ((VersionedLine hashWholeFile) × α)

def SourceIndexedList.insert {α hashWholeFile} (a : α) (i : VersionedLine hashWholeFile) :
    SourceIndexedList α hashWholeFile → SourceIndexedList α hashWholeFile
  | [] => [(i, a)]
  | e :: l =>
    match compare i e.1 with
    | .gt => (i, a) :: e :: l
    | .eq => (i, a) :: l
    | .lt => e :: SourceIndexedList.insert a i l

def SourceIndexedArray (α) (hashWholeFile := false) :=
    Array (Option ((VersionedLine hashWholeFile) × α))

def Array.setPadNone {α} (arr : Array (Option α)) (i : Nat) (a : α) : Array (Option α) :=
  if h : i < arr.size then
    arr.set i a
  else
    (arr.rightpad i none).push a

section setPadNone

variable {α} {arr : Array (Option α)} {i : Nat} {a : α}

@[simp] theorem Array.setPadNone_size : (arr.setPadNone i a).size = max arr.size (i + 1) := sorry

theorem Array.setPadNone_lt_size : i < (arr.setPadNone i a).size := by simp; omega

@[simp] theorem Array.setPadNone_get : (arr.setPadNone i a)[i]'setPadNone_lt_size = some a := sorry

@[simp] theorem Array.setPadNone_get_none {j} (h_size : arr.size ≤ j) (h_i : j < i) :
    (arr.setPadNone i a)[j]'(Nat.lt_trans h_i setPadNone_lt_size) = none := sorry

end setPadNone

def SourceIndexedArray.insert {α hashWholeFile} (a : α) (i : VersionedLine hashWholeFile)
    (arr : SourceIndexedArray α hashWholeFile) : SourceIndexedArray α hashWholeFile :=
  arr.setPadNone i.line (i, a)

def SourceIndexedArray.pruneInvalid {α} (arr : SourceIndexedArray α false) (map : FileMap) :
    SourceIndexedArray α false :=

namespace SourceIndexed

variable {α hashWholeFile} (data : SourceIndexed α hashWholeFile)

def insertAt (ref : Syntax) (map : FileMap) (a : α) (canonicalOnly := false) :
    SourceIndexed α hashWholeFile :=
  match ref.getRange? canonicalOnly with
  | some range => data.insert (range.toVersionedLine map) a
  | none => data

-- Could have something which prunes all invalid data. However, this is largely unnecessary, as the
