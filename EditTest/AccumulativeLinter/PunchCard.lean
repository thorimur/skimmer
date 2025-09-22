import Lean
import EditTest.Lean.Data.Array

/-!
TODO: pick a better metaphor?
-/

inductive PunchCard where
| unfinished | finished | waitedOn (c : Std.Condvar)
deriving Inhabited

/-- This should only be pushed to by `addLinterWithCleanup`. -/
initialize punchCardsRef : IO.Ref (Array PunchCard) ← IO.mkRef #[]

-- !! Should we have a global mutex like this, or make a new mutex each time we wait?
initialize punchCardWaiter : Std.BaseMutex ← Std.BaseMutex.new

def IO.waitForPunched (idx : Nat) : BaseIO Unit := do
  match (← punchCardsRef.get)[idx]! with
  | .finished => return
  | .waitedOn c =>
    punchCardWaiter.lock -- !! Necessary?
    c.wait punchCardWaiter
    punchCardWaiter.unlock
  | .unfinished => do
    let c ← Std.Condvar.new
    let some c ← punchCardsRef.modifyGet fun a =>
      a.modifyGet idx fun
        | .finished => (none, .finished)
        | w@(.waitedOn c) => (some c, w)
        | .unfinished => (some c, .waitedOn c)
      | return
    punchCardWaiter.lock -- !! Necessary?
    c.wait punchCardWaiter
    punchCardWaiter.unlock

def IO.punch (idx : Nat) : BaseIO Unit := do
  let some c ← punchCardsRef.modifyGet fun a =>
    if let .waitedOn c := a[idx]! then
      (some c, a.set! idx .finished)
    else
      (none, a.set! idx .finished)
    | return
  c.notifyAll -- !! Is this significantly worse than `notifyOne`?
