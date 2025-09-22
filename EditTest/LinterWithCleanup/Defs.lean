import EditTest.LinterWithCleanup.RangeRecord

open Lean Elab Command

structure LinterWithCleanup where
  name        : Name := by exact decl_name%
  run         : CommandElab
  /-- Waits for this linter's `run` to finish on all commands, then runs. The current ref is the `eoi` token. -/
  cleanup     : CommandElabM Unit
  -- shouldCleanup : CommandElabM Bool := pure true -- for checking options?
  runOnEOI    : CommandElabM Bool := pure true
  runOnHeader : CommandElabM Bool := pure false

@[inline] def exceptOnEOI (f : CommandElab) : CommandElab := fun stx =>
  unless stx.getKind == ``Parser.Command.eoi do f stx

def LinterWithCleanup.toLinter (l : LinterWithCleanup) (idx : Nat) : Linter where
  name    := l.name
  run stx :=
    unless Elab.inServer.get (← getOptions) do -- Only run noninteractively.
      try exceptOnEOI l.run stx finally IO.recordRange idx stx

initialize lintersWithCleanupRef : IO.Ref (Array LinterWithCleanup) ← IO.mkRef #[]

def addLinterWithCleanup (l : LinterWithCleanup) : IO Unit := do
  let idx ← lintersWithCleanupRef.modifyGet fun a => let idx := a.size; (idx, a.push l)
  punchCardsRef.modify (·.push .unfinished)
  rangeRecordsRef.modify (·.push {})
  addLinter <| l.toLinter idx
