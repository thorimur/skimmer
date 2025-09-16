import EditTest.Accumulator.Reflike
import Batteries

/-!
Possibly we should change this whole design to use a mutex.
-/

inductive DynamicPromise (α : Type) where
/-- Nothing has yet needed to wait on the finished data to be available, so we have not yet created a promise. -/
| noPromise (data : α)
-- Alternatively, we could resolve it with `Unit` and the caller could just check the ref for the data.
/-- The state of the `DynamicPromise` when something is waiting on the finished data to be available. The promise should not be resolved without also changing the state of the `DynamicPromise` to `finished`, and the data held by `.finished` should be the same as that used to resolve the promise. -/
| waitedOn (pr : IO.Promise α) (data : α)
| finished (pr : IO.Promise α)
| finishedNoPromise (data : α)

abbrev DynamicPromiseRef (α : Type) := IO.Ref <| DynamicPromise α

namespace DynamicPromiseRef

def modifyAndResolveIf (f : α → α) (p : α → Bool) (d : DynamicPromiseRef α) : BaseIO Unit := do
  -- Return the promise and final state if we should resolve it.
  let prAndFinishedData? ← d.modifyGet fun
    | .noPromise data => (none, .noPromise (f data))
    | .waitedOn pr data =>
      let data := f data
      if p data then
        (some (pr, data), .finished pr)
      else
        (none, .waitedOn pr data)
    | s => (none, s)
  if let some (pr, data) := prAndFinishedData? then pr.resolve data

def promise? (d : DynamicPromiseRef α) : BaseIO (Option <| IO.Promise α) := do
  -- modifyGet to lock and avoid copying `data` accidentally? or do we never increment the reference count for data?
  match (← d.get) with
  | .waitedOn pr _ | .finished pr => return pr
  | _ => return none

private inductive StatusAfterModify (α : Type) where
| finishedNoPromise (a : α)
| finished (pr : IO.Promise α)
| needsPromise
| shouldResolve (pr : IO.Promise α) (a : α)
| waitFor (pr : IO.Promise α)

def _root_.IO.Promise.resultOrError (pr : IO.Promise α) : IO α := do
  pr.result?.get.getDM <| throw <| IO.userError "Promise was dropped"

-- Really need to check for sharing and the like.
def modifyAndWaitFor [Nonempty α] (f : α → α) (p : α → Bool) (d : DynamicPromiseRef α) : IO α := do
  let r : StatusAfterModify α ← d.modifyGet fun
    | .noPromise data =>
      let data := f data
      if p data then
        (.finishedNoPromise data, .finishedNoPromise data)
      else
        (.needsPromise, .noPromise data)
    | .waitedOn pr data =>
      let data := f data
      if p data then
        (.shouldResolve pr data, .finished pr)
      else
        (.waitFor pr, .waitedOn pr data)
    | s@(.finished pr) => (.finished pr, s)
    | s@(.finishedNoPromise data) => (.finishedNoPromise data, s)
  match r with
  | .finishedNoPromise data => return data
  | .finished pr => pr.resultOrError
  | .needsPromise => do
    -- Wouldn't need to do all this with a lock...
    let pr ← IO.Promise.new
    let prOrData? : IO.Promise α ⊕ α ← d.modifyGet fun
      | .noPromise data => (.inl pr, .waitedOn pr data)
      | s@(.waitedOn pr _) => (.inl pr, s)
      | s@(.finishedNoPromise data) => (.inr data, s)
      | s@(.finished pr) => (.inl pr, s)
    match prOrData? with
    | .inl pr   => pr.resultOrError
    | .inr data => return data
  | .waitFor pr => pr.resultOrError
  | .shouldResolve pr data => do
    pr.resolve data
    pr.resultOrError
