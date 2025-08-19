import Lean
import Batteries
import Init.Data.Range.Polymorphic

open Lean Elab Command

/-!
# Version-tied data

-/

/-- The index for `StatefulLinter` states of the form `SourceIndexed α`.

The `BEq` instance compares only the `line`, so that we are more likely to destroy stale state.

The `hash` ought to be the hash of the file up through the end of the command syntax, so that we can detect if a linter's output is invalid. Note that technically a linter could determine its persistent data by looking at aspects of the environment which are sensitive to concurrency, and so edits below the source syntax might still invaldiate the state. Such linters should hash the entire source. -/
-- Note: could include `hashWholeFile` as a type parameter?
structure VersionedLine where
  /-- The line on which the relevant command syntax starts. -/
  line : Nat
  /-- The position through which to hash the source file. If `none`, use the whole file.

  Note: we do not simply use `source.endPos` since the file may be extended, which ought to invalidate our `VersionedLine`. -/
  endPos : Option String.Pos
  /-- The hash of the source that we want to make sure does not change. -/
  hash : UInt64

/- Can change every `map` to something that works in a `MonadFileMap` monad... -/


/-- Only compares by line. -/
instance VersionedLine.instBEqByLine : BEq VersionedLine where
  beq := (·.line == ·.line)

/-- Only compares by line. -/
instance VersionedLine.instOrdByLine : Ord VersionedLine where
  compare := (compare ·.line ·.line)

/-- Only hashes the `line` (and does not really hash at all, but just represents it as a `UInt64`,
as does the standard `Hashable` instance for `Nat`) -/
instance VersionedLine.instHashableByLine : Hashable VersionedLine where
  hash v := UInt64.ofNat v.line

@[inline] def String.hashRange (s : String) (range : String.Range) : UInt64 :=
  (s.extract range.start range.stop).hash

def String.Range.toVersionedLine (range : String.Range) (map : FileMap) (hashWholeFile := false) :
    VersionedLine where
  line := (map.toPosition range.start).line
  endPos := if hashWholeFile then none else range.stop
  hash := if hashWholeFile then map.source.hash else map.source.hashRange ⟨0, range.stop⟩

def VersionedLine.isValid (v : VersionedLine) (map : FileMap) : Bool :=
  v.hash = if let some endPos := v.endPos then
    map.source.hashRange ⟨0, endPos⟩ else map.source.hash

/- We choose `PersistentHashMap`s because they are extensible and shareable. However, the number of entries is bounded by the number of lines in the file, and the hash of a natural number is the number itself. As such, a simple `List` might be okay. -/

/-- Data of type `α` indexed by a line in the source file. -/
def SourceIndexedPHashMap (α) := PersistentHashMap VersionedLine α

namespace SourceIndexedPHashMap

variable {α} (data : SourceIndexedPHashMap α)

def insertAt? (ref : Syntax) (map : FileMap) (a : α) (canonicalOnly := false)
    (hashWholeFile := false) : Option (SourceIndexedPHashMap α) :=
  ref.getRange? canonicalOnly |>.map fun range =>
    data.insert (range.toVersionedLine map hashWholeFile) a

end SourceIndexedPHashMap

def SourceIndexedList (α) := List (VersionedLine × α)

namespace SourceIndexedList

def insert {α} (i : VersionedLine) (a : α) :
    SourceIndexedList α → SourceIndexedList α
  | [] => [(i, a)]
  | e :: l =>
    match compare i e.1 with
    | .gt => (i, a) :: e :: l
    | .eq => (i, a) :: l
    | .lt => e :: SourceIndexedList.insert i a l

def insertAt? {α} (ref : Syntax) (map : FileMap) (a : α)
    (data : SourceIndexedList α) (canonicalOnly := false)
    (hashWholeFile := false) : Option (SourceIndexedList α) :=
  ref.getRange? canonicalOnly |>.map fun range =>
    data.insert (range.toVersionedLine map hashWholeFile) a

end SourceIndexedList

def SourceIndexedArray (α) := Array (Option (VersionedLine × α))

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

namespace SourceIndexedArray

def insert {α} (i : VersionedLine) (a : α)
    (arr : SourceIndexedArray α) : SourceIndexedArray α :=
  arr.setPadNone i.line (i, a)

def insertAt? {α} (ref : Syntax) (map : FileMap) (a : α)
    (data : SourceIndexedArray α) (canonicalOnly := false)
    (hashWholeFile := false) : Option (SourceIndexedArray α) :=
  ref.getRange? canonicalOnly |>.map fun range =>
    data.insert (range.toVersionedLine map hashWholeFile) a

def filterInvalid {α} (arr : SourceIndexedArray α) (map : FileMap) :
    SourceIndexedArray α :=
  arr.map fun | va@(some (v,_)) => if v.isValid map then va else none | none => none

def foldlOnValid {α} {β : Type v}
    (f : β → α → β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : β :=
  arr.foldl (init := init) fun
    | b, some (v,a) => if v.isValid map then f b a else b
    | b, none => b

def foldlOnValidM {α} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : β → α → m β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : m β :=
  arr.foldlM (init := init) fun
    | b, some (v,a) => if v.isValid map then f b a else pure b
    | b, none => pure b

def foldrOnValid {α} {β : Type v}
    (f : α → β → β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : β :=
  arr.foldr (init := init) fun
    | some (v,a), b => if v.isValid map then f a b else b
    | none, b => b

def foldrOnValidM {α} {β : Type v} {m : Type v → Type w} [Monad m]
    (f : α → β → m β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : m β :=
  arr.foldrM (init := init) fun
    | some (v,a), b => if v.isValid map then f a b else pure b
    | none, b => pure b

end SourceIndexedArray


-- Could have something which prunes all invalid data. However, this is largely unnecessary, as the
