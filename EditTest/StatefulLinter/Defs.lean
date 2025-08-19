import Lean

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
structure StatefulLinter (α) where
  /-- The initial state of the linter's state at initialization. -/
  mkInitial : IO α := by exact (pure {})
  /-- The linter's `run`, taking in the `state : IO.Ref`. -/
  run (state : IO.Ref α) : CommandElab
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
  let data ← IO.mkRef <|← linter.mkInitial
  addLinter (linter.toLinter data)
  return data
