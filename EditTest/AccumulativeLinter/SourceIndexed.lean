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

/-- Whether two ranges are less than each other, greater than each other, or overlap. We do not care whether two ranges are equal.-/
inductive RangeOrdering where
  /-- Less than. -/
  | lt
  /-- Overlapping. -/
  | overlapping
  /-- Greater than. -/
  | gt
deriving Inhabited, DecidableEq, Repr

@[ext]
class RangeOrd (α : Type u) where
  /-- Compare two elements in `α` using the comparator contained in an `[OverlapOrd α]` instance. -/
  compare : α → α → RangeOrdering

def rangeCompare (a : String.Range) (b : String.Range) : RangeOrdering :=
  if b.stop ≤ a.start then .gt else if a.stop ≤ b.start then .lt else .overlapping

/--
The `hash` ought to be the hash of the file up through the end of the command syntax, so that we can detect if a linter's output is invalid. Note that technically a linter could determine its persistent data by looking at aspects of the environment which are sensitive to concurrency, and so edits below the source syntax might still invaldiate the state. Such linters should hash the entire source.
-/
-- Note: could include `hashWholeFile` as a type parameter?
structure String.VersionedRange where
  range : String.Range
  /-- The hash of the source that we want to make sure does not change. Which part of the source we hash (if any) is not recorded in the `VersionedRange`. -/
  hash : UInt64
deriving Inhabited, Repr, DecidableEq

@[inline] def String.hashRange (s : String) (range : String.Range) : UInt64 :=
  (s.extract range.start range.stop).hash

/-- The region that an interactive linter is "sensitive" to. Note that we do not, by default, do any validity checking *before* adding data. This must be managed by the linter. -/
inductive InteractiveTrackingScope where
| upToCommandEnd (withTrailing := false)
| wholeFile

-- What would happen if we specialized to scope, here and in `insert`? Effectively we want one version for none, and one for not none...maybe do that directly?
@[inline] def String.Range.toVersionedRange (range : String.Range) (map : FileMap)
    (scope : Option InteractiveTrackingScope := some .upToCommandEnd) : VersionedRange where
  -- lrange := ⟨map.toPosition range.start, map.toPosition range.stop⟩
  range := range
  hash := scope.elim 0 fun
    | .upToCommandEnd _ => map.source.hashRange ⟨0, range.stop⟩
    | .wholeFile => map.source.hash

@[inline] def String.VersionedRange.isValid (v : String.VersionedRange) (map : FileMap)
    (scope : Option InteractiveTrackingScope := some .upToCommandEnd) : Bool :=
  scope.elim true fun
    | .upToCommandEnd _ => v.hash = map.source.hashRange ⟨0, v.range.stop⟩
    | .wholeFile        => v.hash = map.source.hash

/-!
# SourceIndexed

API is implemented by `IndexesSource` for comparison. We'll probably settle on one.
-/

open String

-- We could have a `List (Option VersionedRange × α)`. Just put `none` if we're not interactive? A bit risky? Even if noninteractive, could be useful to record the ranges...

-- What about `for` vs. fold?
/-- Provides `insert {α : Type} : SourceIndexed α → VersionedRange → α → SourceIndexed α`.
Just to make testing implementations easier. Likely not permanent. -/
class IndexesSource (SourceIndexed : Type → Type) where
  protected getEntry? {α : Type} : SourceIndexed α → String.Range → Option (VersionedRange × α)
  -- Should we use `Option String.Range` here?
  protected insert {α : Type} : SourceIndexed α → String.Range → α → FileMap → Option InteractiveTrackingScope → SourceIndexed α
  protected foldl {α : Type} {β : Type} (data : SourceIndexed α)
    (f : β → VersionedRange → α → β) (init : β) : β
  protected empty {α} : SourceIndexed α := by exact {}

instance {SourceIndexed α} [IndexesSource SourceIndexed] : EmptyCollection (SourceIndexed α) :=
  ⟨IndexesSource.empty⟩

instance {α} {SourceIndexed} [IndexesSource SourceIndexed] : Inhabited (SourceIndexed α) :=
  ⟨IndexesSource.empty⟩

-- Should really just get `original` ranges.
def _root_.Lean.Syntax.getVersionedRange? (ref : Syntax) (map : FileMap)
    (scope : Option InteractiveTrackingScope) (canonicalOnly := true) : Option VersionedRange :=
  let range? := match scope with
  | none | some (.upToCommandEnd false) | some .wholeFile => ref.getRange? canonicalOnly
  | some (.upToCommandEnd true) => ref.getRangeWithTrailing? canonicalOnly
  range?.map (·.toVersionedRange map scope)

def Lean.Syntax.hasValidData {m : Type → Type} [Monad m] [MonadFileMap m] {SourceIndexed}
    [IndexesSource SourceIndexed]
    (ref : Syntax) (state : SourceIndexed α)
    (canonicalOnly := true) : m Bool := do
  let map ← getFileMap
  -- We use `none` here because any `IndexesSource` implementation should not `get` differently based on the hash/endPos.
  let some l := ref.getRange? canonicalOnly | return false
  let some (l,_) := IndexesSource.getEntry? state l | return false
  return l.isValid map

def insertAt? {SourceIndexed} [IndexesSource SourceIndexed] (data : SourceIndexed α) (ref : Syntax) (map : FileMap) (a : α) (canonicalOnly := false)
    (scope : Option InteractiveTrackingScope := some .upToCommandEnd) :
    Option (SourceIndexed α) :=
  ref.getRange? canonicalOnly |>.map (IndexesSource.insert data · a map scope)

def foldlOnValid {α} {SourceIndexed} [IndexesSource SourceIndexed] {β : Type}
    (data : SourceIndexed α)
    (f : β → VersionedRange → α → β) (init : β) (map : FileMap) : β :=
  IndexesSource.foldl data (init := init) fun b v a => if v.isValid map then f b v a else b


-- /- We choose `PersistentHashMap`s because they are extensible and shareable. However, the number of entries is bounded by the number of lines in the file, and the hash of a natural number is the number itself. As such, a simple `List` might be okay. -/

-- /-- Data of type `α` indexed by a line in the source file. -/
-- def SourceIndexedPHashMap (α) := PersistentHashMap VersionedRange α

-- instance : IndexesSource SourceIndexedPHashMap where
--   getEntry? := PersistentHashMap.findEntry?
--   insert := .insert
--   foldl := PersistentHashMap.foldl


def SourceIndexedList (α) := List (VersionedRange × α)

namespace SourceIndexedList

@[inline] def insert {α} (data : SourceIndexedList α) (i : String.Range) (a : α) (map : FileMap)
    (scope : Option InteractiveTrackingScope) : SourceIndexedList α :=
  match data with
  | [] => [(i.toVersionedRange map scope, a)]
  | e :: l =>
    match rangeCompare i e.1.range with
    | .gt => (i.toVersionedRange map scope, a) :: e :: l
    | .overlapping => SourceIndexedList.insert l i a map scope
    | .lt => e :: SourceIndexedList.insert l i a map scope

def getEntry? {α} (data : SourceIndexedList α) (i : String.Range) : Option (VersionedRange × α) :=
  data.find? (·.1.range == i)

instance : IndexesSource SourceIndexedList where
  getEntry?
  insert
  foldl l f init := l.foldl (init := init) fun acc (v, a) => f acc v a
  empty := []

end SourceIndexedList

section Contiguity

/-!
# Contiguity of commands

Since we cannot wait for all commands, we need a way of determining if every command has been linted. We should probably include a timeout just in case.

There are a couple approaches we could take here. We'll start noninteractively.

We'll assume that commands are disjoint and contiguous, but TODO: see where parsing actually starts.

Once we have the start of the first command, we can employ a couple different strategies, depending on what invariants we have.
- **Noninteractive**:
  - (Assuming each command is elaborated only once) Each linter adds the size of a range to a counter. The cleanup checks when the size reaches its position, and waits in between.
    - If not, we can have an auxiliary hash set with ranges to see if we've elaborated it before. Note we'd want to decrement the counter as soon as we see a range again, so we know to wait ASAP. Not perfect.
  - We insert the range into an RBTree. The cleanup checks if the tree is contiguous up to its position.
  - Have a structure which tracks both gaps and contiguous ranges, marked as such. We want it to be (1) quick to insert new ranges (2) quick to know when there are any gaps up to our cleanup posiiton. Interactively (3) we want to obliterate stale overlapping ranges and easily (4) check for validity of the ranges.
  - A little 1D algebraic topology: conceptualize the start points as -p and the stop points as +p. Gluing a new range means adding -p₀ + p₁ to the boundary of the overall shape. Our operations are `get?` and `erase?`. We might actually want to unlinearize a little and store stop points in one set and start points in another; stop points erase from the start set else add to the stop set, and vice versa. If every command only gets elaborated once, we can combine our start and stop sets and work in ℤ₂. However, we should also keep a running total of the number of points, positive or negative. We can just check if the number of points is 2, and if 0 is in the set and the endPos is in the set. Else, wait. This doesn't work at all for interactivity, unfortunately.
- **Interactive**:
  - We insert hashed(?) .start/.stop positions into an RBTree. We obliterate things in between in real time.
  - We have some sort of "contiguous block structure/tree" which caches the range of the contiguity at the node for quick checking by the cleanup.
  - There's a chance that `SourceIndexedList` is fine.
  - We can have an `Array` whose indices refer to blocks of positions of some size[Copilot:, and each entry is a `List` of ranges in that block. We can cache the contiguity of each block, and the cleanup can check the blocks up to its position.] Can we iterate this idea and have multiple stages of blocks? I'm wondering what happens when things are in different blocks. It might be easy to invalidate whole blocks at once in a tree-like setup.

Note that the `eoi` token has weird position info: `⟨startPos, 0⟩` if we `getRangeWithTrailing`. We should check for this in the accumulative linter infrastructure, or possibly ask for eoi to be handled separately anyway

Or, we could add `⟨0,headerEndPos⟩` to the set at the start of the cleanup, then just check for it to have 0 elements. I like that. Means no special handling! Should have a test that internals for `eoi` don't change though. Or: just handle the insertion of eoi separately, and ensure that we use the "weird" version. After all, the "real" version doesn't make sense--we'd have to ensure the eoi token was captured anyway.

We also manually run the linter in question on the eoi token, since otherwise it runs after. All the more reason for it to not *actually* run on the eoi token, but be a separate thing the cleanup calls.
-/


namespace Noninteractive

def RangeBoundariesMod2 := Std.HashSet String.Pos

namespace RangeBoundariesMod2

def insertMod2 (m : RangeBoundariesMod2) (k : String.Pos) : RangeBoundariesMod2 :=
  if m.contains k then m.erase k else m.insert k

def insertRange (m : RangeBoundariesMod2) (r : String.Range) : RangeBoundariesMod2 :=
  m.insertMod2 r.start |>.insertMod2 r.stop

def isRange (m : RangeBoundariesMod2) (start stop : String.Pos) : Bool :=
  m.size = 2 && m.contains start && m.contains stop

@[inline] def isCycle (m : RangeBoundariesMod2) : Bool :=
  m.size = 0

end RangeBoundariesMod2

/-- Assumes that the linter has already run on the eoi token--specifically, the cleanup should have manually run it, since cleanups happen during elaboration of `eoi`, and thus prior to the linter. -/
def waitForAllCommands (rangeRef : IO.Ref RangeBoundariesMod2) (name : Name) (sleep : UInt32 := 500) (numSleeps : Nat := 1000) : CommandElabM Unit :=
match numSleeps with
| 0 => logWarning m!"{name}: Timed out waiting for all commands to be linted"
| numSleeps+1  => do
  unless (← rangeRef.get).isCycle do
    _ ← IO.sleep sleep
    waitForAllCommands rangeRef name sleep numSleeps

end Noninteractive





















-- def SourceIndexedArray (α) := Array (Option (VersionedRange × α))

-- -- TODO: Does this exist somewhere?
-- def Array.setPadNone {α} (arr : Array (Option α)) (i : Nat) (a : α) : Array (Option α) :=
--   if h : i < arr.size then
--     arr.set i a
--   else
--     (arr.rightpad i none).push a

-- section setPadNone

-- variable {α} {arr : Array (Option α)} {i : Nat} {a : α}

-- @[simp] theorem Array.setPadNone_size : (arr.setPadNone i a).size = max arr.size (i + 1) := sorry

-- theorem Array.setPadNone_lt_size : i < (arr.setPadNone i a).size := by simp; omega

-- @[simp] theorem Array.setPadNone_get : (arr.setPadNone i a)[i]'setPadNone_lt_size = some a := sorry

-- @[simp] theorem Array.setPadNone_get_none {j} (h_size : arr.size ≤ j) (h_i : j < i) :
--     (arr.setPadNone i a)[j]'(Nat.lt_trans h_i setPadNone_lt_size) = none := sorry

-- end setPadNone

-- namespace SourceIndexedArray

-- def insert {α} (arr : SourceIndexedArray α) (i : VersionedRange) (a : α)
--     : SourceIndexedArray α :=
--   arr.setPadNone i.line (i, a)

-- def getEntry? {α} (data : SourceIndexedArray α) (i : VersionedRange) : Option (VersionedRange × α) :=
--   (show Array _ from data)[i.line]?.join

-- -- `for` vs. `foldl`?
-- -- what about `reduceOption` first? is there `reduceOptionMap` somewhere?
-- instance : IndexesSource SourceIndexedArray where
--   getEntry? := getEntry?
--   insert := insert
--   foldl arr f init := arr.foldl (init := init) fun
--     | b, some (v,a) => f b v a
--     | b, none => b
--   empty := #[]

-- def filterInvalid {α} (arr : SourceIndexedArray α) (map : FileMap) :
--     SourceIndexedArray α :=
--   arr.map fun | va@(some (v,_)) => if v.isValid map then va else none | none => none

-- def foldlOnValid {α} {β : Type v}
--     (f : β → α → β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : β :=
--   arr.foldl (init := init) fun
--     | b, some (v,a) => if v.isValid map then f b a else b
--     | b, none => b

-- def foldlOnValidM {α} {β : Type v} {m : Type v → Type w} [Monad m]
--     (f : β → α → m β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : m β :=
--   arr.foldlM (init := init) fun
--     | b, some (v,a) => if v.isValid map then f b a else pure b
--     | b, none => pure b

-- def foldrOnValid {α} {β : Type v}
--     (f : α → β → β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : β :=
--   arr.foldr (init := init) fun
--     | some (v,a), b => if v.isValid map then f a b else b
--     | none, b => b

-- def foldrOnValidM {α} {β : Type v} {m : Type v → Type w} [Monad m]
--     (f : α → β → m β) (init : β) (arr : SourceIndexedArray α) (map : FileMap) : m β :=
--   arr.foldrM (init := init) fun
--     | some (v,a), b => if v.isValid map then f a b else pure b
--     | none, b => pure b

-- end SourceIndexedArray


-- Could have something which prunes all invalid data. However, this is largely unnecessary, as the
