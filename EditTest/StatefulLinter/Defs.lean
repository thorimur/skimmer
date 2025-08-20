import Lean
import EditTest.StatefulLinter.SourceIndexed

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
structure StatefulLinter (β) where
  /-- The initial state of the linter's state at initialization. -/
  mkInitialRefState : IO β := by exact (pure {})
  /-- The linter's `run`, taking in the `state : IO.Ref`. -/
  run (state : IO.Ref β) : CommandElab
  /-- The name of the linter. -/
  name : Name := by exact decl_name%

/-- Given some `IO.Ref` which the `StatefulLinter` should use as its state, create a regular `Linter`. -/
def StatefulLinter.toLinter (linter : StatefulLinter α) (ref : IO.Ref α) : Linter where
  run := linter.run ref
  name := linter.name

/-- Adds `linter` as a linter, creating and returning the `IO.Ref` that holds its state.

Usage:
```
initialize fooState : IO.Ref ← addStatefulLinter linter
```
-/
def addStatefulLinter (linter : StatefulLinter α) : IO (IO.Ref α) := do
  let data ← IO.mkRef <|← linter.mkInitialRefState
  addLinter (linter.toLinter data)
  return data

structure PersistentStatefulLinter (α) (β) (σ) extends StatefulLinter β where
  /-- The extension that stores the data. -/
  ext : PersistentEnvExtension α β σ -- Or should it be a Descr? After all, the `StatefulLinter` does not have its `IO.Ref`, but takes it in as an argument.

structure PersistentStatefulLinterDescr (α) (β) (σ) extends PersistentEnvExtensionDescr α β σ, StatefulLinter β where
  cleanupName : Name := by exact (decl_name% ++ cleanup)

def PersistentStatefulLinter.toCleanup {α β σ}
    (r : IO.Ref β) (ext : PersistentEnvExtension α β σ) : CommandElab := fun _ => do
  -- should we use modifyEnv?
  setEnv <| ext.addEntry (← getEnv) (← r.get)


structure SimplePersistentStatefulLinterDescr (β) (α) where
  name                  : Name := by exact decl_name%
  exportEntriesFnEx     : Environment → β → OLeanLevel → Array α
  statsFn               : β → Format := fun _ => Format.nil
  -- include replay??


-- Interactive capabilities should register two linters + an option such that each uses the same ref (thus two `addLinter`, but not two `addStatefulLinter`) and we check the option in each.
-- However, this means we actually don't want `run`, but something like `record : CommandElabM (Option α)`. The infrastructure here then packages it into a (regular) linter's `run`. Something like: `AccumulativeLinter`? Can we rely on linters only running once in a noninteractive context? Because then we might actually want two refs; one could be source indexed, and one could just be an Array. Argh.


-- Note that any option controlling the whole linter should also control the persistence.

structure AccumulativeLinter (β) (α) where
  /-- Records a value of type `β` for a given command (or not). -/
  record : CommandElabM (Option β)
  /-- At the end of the file, appends each recorded value to the exported state. -/
  append : Array α → VersionedLine × β → Array α
  trackingScope : TrackingScope := .upToCommandEnd
  name : Name := by exact decl_name%

def addAccumulativeLinter {α} (l : AccumulativeLinter α) : IO (IO.Ref (SourceIndexedArray α))

/-

initialize myRef ← addStatefulLinter myStatefulLinter
initialize myExt ← registerPersistentEnvExtension myPersistentEnvExtensionDescr

@[cleanup]
def myLinter.cleanup : CommandElab := toCleanup myRef myExt

-/
