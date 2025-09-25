/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Lean.Data.Array

/-!
TODO: pick a better metaphor?
-/

inductive PunchCard where
| unfinished | finished | waitedOn
deriving Inhabited

@[inline] def PunchCard.isFinished : PunchCard → Bool
  | .finished => true
  | _         => false

/-- This should only be pushed to by `addLinterWithCleanup`. -/
initialize punchCardsRef : IO.Ref (Array PunchCard) ← IO.mkRef #[]

/- We potentially read the reference more times than we'd like with this, but that shouldn't be awful, especially since in most cases there is only one `waitedOn` at a time. -/

/-- This bell is rung each time something which has been `waitedOn` finishes. -/
initialize punchCardBell : Std.Condvar ← Std.Condvar.new

-- !! Should we have a global mutex like this, or make a new mutex each time we wait?
initialize punchCardWaiter : Std.BaseMutex ← Std.BaseMutex.new

def IO.waitUntilPunched! (idx : Nat) : BaseIO Unit :=
  unless (← punchCardsRef.get)[idx]!.isFinished do
    let mustWait ← punchCardsRef.modifyGet fun a =>
      match a[idx]! with
      | .waitedOn   => (true,  a)
      | .unfinished => (true,  a.set! idx .waitedOn)
      | .finished   => (false, a)
    if mustWait then
      punchCardWaiter.lock
      punchCardBell.waitUntil punchCardWaiter <| return (← punchCardsRef.get)[idx]!.isFinished
      punchCardWaiter.unlock

def IO.punch! (idx : Nat) : BaseIO Unit := do
  let shouldRingBell ← punchCardsRef.modifyGet fun a =>
    match a[idx]! with
    | .waitedOn   => (true,  a.set! idx .finished)
    | .unfinished => (false, a.set! idx .finished)
    | .finished   => (false, a)
  -- We lock the mutex in case we'd be notifying while the predicate is being checked, before we re-wait.
  if shouldRingBell then punchCardWaiter.lock; punchCardBell.notifyAll; punchCardWaiter.unlock
