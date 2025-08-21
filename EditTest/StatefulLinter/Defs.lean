import Lean
import EditTest.StatefulLinter.SourceIndexed
import EditTest.StatefulLinter.Reflike

open Lean Elab Command

/-!
# Modifying dynamic data with linters

Linters cannot modify the environment, since they are run within `withoutModifyingEnv`. However, they can modify `IO.Ref`s. While concurrency is an issue here, we simply have to deal with it if we have any hope of extracting data from them.

We provide a couple of options for doing so. We try to account for interactivity if possible.

- TODO: We allow either `Std.Mutex`es or `IO.Ref`s.
- TODO: We allow "history-sensitive" storage such that stored data can be validated as coming from a current version of the file, or allow this to be turned off as an optimization.
  - TODO: We allow intermittent (in time or size?) size checks on the reflike, and garbage collect then.

-/

section Linter

/--
A linter which references some `IO.Ref` as a state during linting.

Linters which are expected to run during interactive editing should use a state of type `SourceIndexed α`.
-/
structure StatefulLinter (β) (Ref : Type → Type) [Reflike Ref] where
  /-- The initial state of the linter's state at initialization. -/
  mkInitialRefState : IO β := by exact (pure {})
  /-- The linter's `run`, taking in the `state : IO.Ref`. -/
  run (state : Ref β) : CommandElab
  /-- The name of the linter. -/
  name : Name := by exact decl_name%

/-- Given some `IO.Ref` which the `StatefulLinter` should use as its state, create a regular `Linter`. -/
def StatefulLinter.toLinter {α Ref} [Reflike Ref] (linter : StatefulLinter α Ref)
    (ref : Ref α) : Linter where
  run := linter.run ref
  name := linter.name

/-- Adds `linter` as a linter, creating and returning the `IO.Ref` that holds its state.

Usage:
```
initialize fooState : IO.Ref ← addStatefulLinter linter
```
-/
def addStatefulLinter {α Ref} [Reflike Ref] (linter : StatefulLinter α Ref) (addLinter := true) :
    IO (Ref α) := do
  let data ← Reflike.new <|← linter.mkInitialRefState
  if addLinter then Command.addLinter (linter.toLinter data)
  return data

structure PersistentStatefulLinter (α) (β) (σ) (Ref) [Reflike Ref] extends StatefulLinter β Ref where
  /-- The extension that stores the data. -/
  ext : PersistentEnvExtension α β σ -- Or should it be a Descr? After all, the `StatefulLinter` does not have its `IO.Ref`, but takes it in as an argument.

structure PersistentStatefulLinterDescr (α) (β) (σ) (Ref) [Reflike Ref] extends
    PersistentEnvExtensionDescr α β σ, StatefulLinter β Ref where
  cleanupName : Name := by exact (decl_name% ++ cleanup)

def PersistentStatefulLinter.toCleanup {α β σ} {Ref} [Reflike Ref]
    (r : Ref β) (ext : PersistentEnvExtension α β σ) : CommandElab := fun _ => do
  -- should we use modifyEnv?
  setEnv <| ext.addEntry (← getEnv) (← Reflike.get r)

structure SimplePersistentStatefulLinterDescr (β) (α) where
  name                  : Name := by exact decl_name%
  exportEntriesFnEx     : Environment → β → OLeanLevel → Array α
  statsFn               : β → Format := fun _ => Format.nil
  -- include replay??


-- Interactive capabilities should register two linters + an option such that each uses the same ref (thus two `addLinter`, but not two `addStatefulLinter`) and we check the option in each.
-- However, this means we actually don't want `run`, but something like `record : CommandElabM (Option α)`. The infrastructure here then packages it into a (regular) linter's `run`. Something like: `AccumulativeLinter`? Can we rely on linters only running once in a noninteractive context? Because then we might actually want two refs; one could be source indexed, and one could just be an Array. Argh.


-- Note that any option controlling the whole linter should also control the persistence.

structure AccumulativeLinterDescr (β) (α) where
  /-- Records a value of type `β` for a given command (or not). -/
  -- allow access to ref?
  record : Syntax → CommandElabM (Option β)
  /-- At the end of the file, appends each recorded value to the exported state. -/
  append : Array α → VersionedLine × β → Array α
  /-- Note: a value of `noninteractive` here will -/
  interactiveTrackingScope : InteractiveTrackingScope := .upToCommandEnd
  statsFn : Array α → Format := fun arr =>
    f!"Recording {arr.size} {if arr.size = 1 then "entry" else "entries"}"
  name : Name := by exact decl_name%

structure AccumulativeLinter (β) (α) (SourceIndexed) [IndexesSource SourceIndexed]
    (Ref : Type → Type) extends AccumulativeLinterDescr β α where
  ref : Ref (SourceIndexed β)
  ext : PersistentEnvExtension α (Array α) (Array α)

namespace AccumulativeLinterDescr

def toPersistentEnvExtensionDescr {α β} (a : AccumulativeLinterDescr β α) :
    PersistentEnvExtensionDescr α (Array α) (Array α) where
  name := a.name ++ `ext
  mkInitial := pure #[]
  addImportedFn _ := pure #[]
  addEntryFn _ new := new -- ignore prior state, since this is only called once
  exportEntriesFnEx _ a _ := a -- allow oleanlevel-dependent behavior?
  statsFn := a.statsFn
  asyncMode := .sync
  replay? := none

elab "#in_server" : command => do
  logInfo m!"{← getBoolOption Elab.inServer.name Elab.inServer.defValue}"

def getTrackingScope {β α} {m : Type → Type} [Monad m] [MonadOptions m]
    (a : AccumulativeLinterDescr β α) : m (Option InteractiveTrackingScope) := do
  if ← getBoolOption Elab.inServer.name Elab.inServer.defValue then
    return some a.interactiveTrackingScope
  else
    return none

def toStatefulLinter
    (Ref : Type → Type) [Reflike Ref] {α β}
    (SourceIndexed) [IndexesSource SourceIndexed]
    (a : AccumulativeLinterDescr β α) : StatefulLinter (SourceIndexed β) Ref where
  run r stx := do
    let some b ← a.record stx | return
    let some vline := stx.getVersionedLine? (← getFileMap) (← a.getTrackingScope)
      | throwError "Could not get range for {stx}"
    Reflike.modify r fun state => IndexesSource.insert state vline b
  name := a.name

end AccumulativeLinterDescr

def addAccumulativeLinter {α β} (a : AccumulativeLinterDescr β α)
    (Ref : Type → Type) [Reflike Ref]
    (SourceIndexed := SourceIndexedArray) [IndexesSource SourceIndexed] (addLinter := true) :
    IO (AccumulativeLinter β α SourceIndexed Ref) := do
  let ref ← addStatefulLinter (addLinter := addLinter) <| a.toStatefulLinter Ref SourceIndexed
  let ext ← registerPersistentEnvExtension a.toPersistentEnvExtensionDescr
  return { a with ref, ext }

def AccumulativeLinter.toCleanup {β α SourceIndexed Ref}
    [IndexesSource SourceIndexed] [Reflike Ref]
    (a : AccumulativeLinter β α SourceIndexed Ref) : CommandElab := fun _ => do
  -- should we use modifyEnv or setEnv?
  let recorded ← Reflike.get a.ref
  let exported := IndexesSource.foldl recorded (init := #[]) fun arr v b =>
    a.append arr (v, b)
  modifyEnv fun env => a.ext.addEntry env exported

/-

initialize myRef ← addStatefulLinter myStatefulLinter
initialize myExt ← registerPersistentEnvExtension myPersistentEnvExtensionDescr

@[cleanup]
def myLinter.cleanup : CommandElab := toCleanup myRef myExt

-/
