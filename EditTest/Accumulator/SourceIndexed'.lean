import Lean
import Batteries
import Init.Data.Range.Polymorphic

open Lean Elab Command

/-!
# Version-tied data

Note that multiple commands might exist on the same line. However, lines are still kind of useful; they give us a way to check for overlaps quickly.

-/

protected structure Lean.Range where
  start : Lean.Position
  stop : Lean.Position
deriving Inhabited, Repr, DecidableEq

deriving instance DecidableEq for String.Range

/-- The index for `StatefulLinter` states of the form `SourceIndexed α`.

The `BEq` instance compares only the `line`, so that we are more likely to destroy stale state.

The `hash` ought to be the hash of the file up through the end of the command syntax, so that we can detect if a linter's output is invalid. Note that technically a linter could determine its persistent data by looking at aspects of the environment which are sensitive to concurrency, and so edits below the source syntax might still invaldiate the state. Such linters should hash the entire source. -/
-- Note: could include `hashWholeFile` as a type parameter?
structure VersionedRange where
  /-- The line on which the relevant command syntax starts. -/
  lrange : Lean.Range
  range : String.Range
  hashWholeFile := false
  /-- The hash of the source that we want to make sure does not change. -/
  hash : UInt64
deriving Inhabited, Repr, DecidableEq

@[inline] def String.hashRange (s : String) (range : String.Range) : UInt64 :=
  (s.extract range.start range.stop).hash

/-- The region that an interactive linter is "sensitive" to. Note that we do not, by default, do any validity checking *before* adding data. This must be managed by the linter. -/
inductive InteractiveTrackingScope where
| upToCommandEnd
| upToCommandEndWithTrailing
| wholeFile

def String.Range.toVersionedRange (range : String.Range) (map : FileMap)
    (scope : Option InteractiveTrackingScope := some .upToCommandEnd) : VersionedRange where
  lrange := ⟨map.toPosition range.start, map.toPosition range.stop⟩
  range := range
  hash := scope.elim 0 fun
    | .upToCommandEnd | .upToCommandEndWithTrailing => map.source.hashRange ⟨0, range.stop⟩
    | .wholeFile => map.source.hash

@[inline] def Lean.FileMap.computeHash (endPos : Option String.Pos) (map : FileMap) : UInt64 :=
  if let some endPos := endPos then
    if endPos = 0 then 0 else map.source.hashRange ⟨0, endPos⟩
  else map.source.hash

def VersionedRange.isValid (v : VersionedRange) (map : FileMap) : Bool :=
  v.hash = (map.computeHash <| if v.hashWholeFile then none else some v.range.stop)

/-!
# SourceIndexed

API is implemented by `IndexesSource` for comparison. We'll probably settle on one.
-/

-- What about `for` vs. fold?
/-- Provides `insert {α : Type} : SourceIndexed α → VersionedRange → α → SourceIndexed α`.
Just to make testing implementations easier. Likely not permanent. -/
class IndexesSource (SourceIndexed : Type → Type) where
  -- Should return `some` even if the `VersionedRange` provided is not valid.
  protected getEntry? {α : Type} : SourceIndexed α → VersionedRange → Option (VersionedRange × α)
  protected insert {α : Type} : SourceIndexed α → VersionedRange → α → SourceIndexed α
  protected foldl {α : Type} {β : Type} (data : SourceIndexed α)
    (f : β → VersionedRange → α → β) (init : β) : β
  protected empty {α} : SourceIndexed α := by exact {}

instance {SourceIndexed α} [IndexesSource SourceIndexed] : EmptyCollection (SourceIndexed α) :=
  ⟨IndexesSource.empty⟩

instance {α} {SourceIndexed} [IndexesSource SourceIndexed] : Inhabited (SourceIndexed α) :=
  ⟨IndexesSource.empty⟩

def _root_.Lean.Syntax.getVersionedRange? (ref : Syntax) (map : FileMap)
    (scope : Option InteractiveTrackingScope) (canonicalOnly := false) : Option VersionedRange :=
  let range? := match scope with
  | none | some .upToCommandEnd | some .wholeFile => ref.getRange? canonicalOnly
  | some .upToCommandEndWithTrailing => ref.getRangeWithTrailing? canonicalOnly
  range?.map (·.toVersionedRange map scope)

def Lean.Syntax.hasValidData {m : Type → Type} [Monad m] [MonadFileMap m] {SourceIndexed}
    [IndexesSource SourceIndexed]
    (ref : Syntax) (state : SourceIndexed α)
    (canonicalOnly := false) : m Bool := do
  let map ← getFileMap
  -- We use `none` here because any `IndexesSource` implementation should not `get` differently based on the hash/endPos.
  let some l := ref.getVersionedRange? map none canonicalOnly | return false
  let some (l,_) := IndexesSource.getEntry? state l | return false
  return l.isValid map


def insertAt? {SourceIndexed} [IndexesSource SourceIndexed] (data : SourceIndexed α) (ref : Syntax) (map : FileMap) (a : α) (canonicalOnly := false)
    (scope : Option InteractiveTrackingScope := some .upToCommandEnd) :
    Option (SourceIndexed α) :=
  ref.getVersionedRange? map scope canonicalOnly |>.map (IndexesSource.insert data · a)

-- Ok do this

def foldlOnValid {α} {SourceIndexed} [IndexesSource SourceIndexed] {β : Type}
    (data : SourceIndexed α)
    (f : β → VersionedRange → α → β) (init : β) (map : FileMap) : β :=
  IndexesSource.foldl data (init := init) fun b v a => if v.isValid map then f b v a else b


/- We choose `PersistentHashMap`s because they are extensible and shareable. However, the number of entries is bounded by the number of lines in the file, and the hash of a natural number is the number itself. As such, a simple `List` might be okay. -/

/-- Data of type `α` indexed by a line in the source file. -/
def SourceIndexedPHashMap (α) := PersistentHashMap VersionedRange α

instance : IndexesSource SourceIndexedPHashMap where
  getEntry? := PersistentHashMap.findEntry?
  insert := .insert
  foldl := PersistentHashMap.foldl


def SourceIndexedList (α) := List (VersionedRange × α)

namespace SourceIndexedList

def insert {α} (data : SourceIndexedList α) (i : VersionedRange) (a : α) : SourceIndexedList α :=
  match data with
  | [] => [(i, a)]
  | e :: l =>
    match compare i e.1 with
    | .gt => (i, a) :: e :: l
    | .eq => (i, a) :: l
    | .lt => e :: SourceIndexedList.insert l i a

def getEntry? {α} (data : SourceIndexedList α) (i : VersionedRange) : Option (VersionedRange × α) :=
  data.find? (·.1 == i)

instance : IndexesSource SourceIndexedList where
  getEntry?
  insert
  foldl l f init := l.foldl (init := init) fun acc (v, a) => f acc v a
  empty := []

end SourceIndexedList

def SourceIndexedArray (α) := Array (Option (VersionedRange × α))

-- TODO: Does this exist somewhere?
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

def insert {α} (arr : SourceIndexedArray α) (i : VersionedRange) (a : α)
    : SourceIndexedArray α :=
  arr.setPadNone i.line (i, a)

def getEntry? {α} (data : SourceIndexedArray α) (i : VersionedRange) : Option (VersionedRange × α) :=
  (show Array _ from data)[i.line]?.join

-- `for` vs. `foldl`?
-- what about `reduceOption` first? is there `reduceOptionMap` somewhere?
instance : IndexesSource SourceIndexedArray where
  getEntry? := getEntry?
  insert := insert
  foldl arr f init := arr.foldl (init := init) fun
    | b, some (v,a) => f b v a
    | b, none => b
  empty := #[]

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
