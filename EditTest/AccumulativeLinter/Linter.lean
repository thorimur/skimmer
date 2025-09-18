import Lean
import Batteries
import EditTest.AccumulativeLinter.SourceIndexed

/-!
1. An accumulative linter could provide a `run : CommandElabM (Option α)` (or `α`), or `run : CommandElabM (Option (α → α))`, or `CommandElabM (Option (α → β))` with some way to modify the state `modify : α → β → α` like `addEntry`. But I worry that's too inflexible. Maybe as a preset? The base should just ask for some ordinary `run`, and we should provide API to modify the full state in a range-recording way. One other option is to decouple the range recording from the data, which breaks some invariants, but if it's hidden from the user, that's fine.

Let's write it then refactor later. Let's decouple things.

Is there a cost to multiple refs (one for each linter)? Should we consolidate?

Splitting the range recording from the data makes it easier to use different types of reflike objects for the data; an IO.Ref is sufficient for the ranges, I believe.

We wrap the provided `run` in `exceptOnEOI` and run it on `eoi` manually, since otherwise it would run after the cleanup which it needs to run prior to.

Maybe we can use a `BaseMutex` to take advantage of `CondVar` without actually locking the `BaseMutex` or anything. After all, we just need to notify the thread. But is this really better? Or is a mutex nicer? Or a `DynamicPromise`?

It might be worth thinking about what should happen in the interactive case. There, we really need indexing by ranges. If we can update the contiguous section somehow, that might be good. The question is what notifies what, where we validate the contiguity, etc.

-/

open Lean Elab Command

/-
Possible designs:
1. There's a single `recordRef` that every accumulative linter adds to, with each point indexed by its name. The cleanup adds every accumulative linter to it after running (or not) it on the header and EOI.
  - This means we wait for *every* marked linter to finish before starting cleanups. I'm not sure about this...after all, linters run in parallel to the elab_rules.
  - Alternatively, what if we had a single ref, but with a hashset for each name? that seems a little better?
2. Possibly, every accumulative linter has its own bespoke action it might do during the cleanup? And we persist to an env extension only in the presets. This sounds good; this is abstractly similar to the notion of an Accumulator I liked before. Perhaps we need a version of `waitFor` so that cleanups could wait for other linters to finish too.

3. For synchronization: the cleanup thread should wait on the first linter to finish. It should check some global punch card to see if each is ready in turn. If not, it should store some wakeup callback in the given linter's place on the punch card, sleeping until woken up. then the linter punches it when finishing, waking up the cleanup thread. It could store the condvar and wait on it, perhaps? Or it could somehow bind its own thread to a task stored there? Not sure.
-/

structure LinterWithCleanup where
  name        : Name := by exact decl_name%
  run         : CommandElab
  /-- Waits for this linter's `run` to finish on all commands, then runs. The current ref is the `eoi` token. -/
  cleanup     : CommandElabM Unit
  runOnEOI    : CommandElabM Bool := pure true
  runOnHeader : CommandElabM Bool := pure false

@[inline] def exceptOnEOI (f : CommandElab) : CommandElab := fun stx =>
  unless stx.getKind == ``Parser.Command.eoi do f stx

def updateRecordRef (n : Name) (stx : Syntax) : BaseIO Unit := sorry

def LinterWithCleanup.toLinter (l : LinterWithCleanup) : Linter where
  name    := l.name
  run stx := do exceptOnEOI l.run stx; updateRecordRef l.name stx

initialize lintersWithCleanupRef : IO.Ref (Array LinterWithCleanup) ← IO.mkRef #[]

def addLinterWithCleanup (l : LinterWithCleanup) : IO Unit := do
  lintersWithCleanupRef.modify (·.push l)
  addLinter l.toLinter
