import EditTest.LinterWithCleanup.Run

/-!
We provide a way to construct a `LinterWithCleanup` that handles an `IO.Ref`.
-/

open Lean Elab Command

structure PersistentRef (ρ κ) where
  ref     : IO.Ref κ
  add     : ρ → κ → κ
  persist : κ → Environment → Environment

structure PersistentLinter (ρ κ) extends PersistentRef ρ κ where
  produce? : Syntax → CommandElabM (Option ρ)
  runOnEOI : CommandElabM Bool := pure true
  runOnHeader : CommandElabM Bool := pure false

def PersistentLinter.toLinterWithCleanup (l : PersistentLinter ρ κ) : LinterWithCleanup where
  run stx := do
    let some v ← l.produce? stx | return
    l.ref.modify (l.add v)
  cleanup := do
    let k ← l.ref.get
    modifyEnv (l.persist k)
  runOnEOI    := l.runOnEOI
  runOnHeader := l.runOnHeader
