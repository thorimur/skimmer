import Skimmer.LinterWithCleanup.RangeRecord

open Lean Elab Command

-- We use this elsewhere repeatedly, in `*Descr`s, so factor it out.
structure LinterWithCleanupSettings where
  shouldCleanup : CommandElabM Bool := pure true
  runOnEOI    : CommandElabM Bool := pure true
  runOnHeader : CommandElabM Bool := pure false
deriving Inhabited

structure LinterWithCleanup extends LinterWithCleanupSettings where
  name        : Name := by exact decl_name%
  run         : CommandElab
  /-- Waits for this linter's `run` to finish on all commands, then runs. The current ref is the `eoi` token. -/
  cleanup     : CommandElabM Unit
deriving Inhabited

@[inline] def exceptOnEOI (f : CommandElab) : CommandElab := fun stx =>
  unless stx.isOfKind ``Parser.Command.eoi do f stx

def LinterWithCleanup.toLinter (l : LinterWithCleanup) (idx : Nat) : Linter where
  name    := l.name
  run stx :=
    -- Only run noninteractively. Assumes `Elab.inServer` is never wrong.
    unless Elab.inServer.get (← getOptions) do
      -- Use the `cmdPos` for the start position to handle `#guard_msgs` correctly.
      try exceptOnEOI l.run stx finally recordRange idx stx (useCmdPos := true)

initialize lintersWithCleanupRef : IO.Ref (Array LinterWithCleanup) ← IO.mkRef #[]

def addLinterWithCleanup (l : LinterWithCleanup) : IO Unit := do
  let idx ← lintersWithCleanupRef.modifyGet fun a => let idx := a.size; (idx, a.push l)
  punchCardsRef.modify (·.push .unfinished)
  rangeRecordsRef.modify (·.push {})
  addLinter <| l.toLinter idx
