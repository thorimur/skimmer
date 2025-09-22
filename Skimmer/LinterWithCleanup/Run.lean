import Skimmer.Cleanup.Elab
import Skimmer.LinterWithCleanup.Defs

open Lean Elab Command

/--
Only to be used when running linters with cleanup manually, outside of `runLinters`. Replicates loop of `runLinters`.

Does *not* update the `rangeRecordsRef`.
-/
def LinterWithCleanup.runOn (linter : LinterWithCleanup) (stx : Syntax) : CommandElabM Unit := do
  withTraceNode `Elab.lint (fun _ => return m!"running linter: {.ofConstName linter.name}")
      (tag := linter.name.toString) do
    let savedState ← get
    try
      linter.run stx
    catch ex =>
      match ex with
      | Exception.error ref msg =>
        logException (.error ref m!"linter {.ofConstName linter.name} failed: {msg}")
      | Exception.internal _ _ =>
        logException ex
    finally
      -- TODO: it would be good to preserve even more state (#4363) but preserving info
      -- trees currently breaks from linters adding context-less info nodes
      modify fun s => { savedState with messages := s.messages, traceState := s.traceState }

namespace Lean.Parser

def parseHeaderRaw (inputCtx : InputContext) : IO Syntax := do
  let dummyEnv ← mkEmptyEnvironment
  let p   := andthenFn whitespace Module.header.fn
  let tokens := Module.updateTokens (getTokenTable dummyEnv)
  let s   := p.run inputCtx { env := dummyEnv, options := {} } tokens (mkParserState inputCtx.inputString)
  if s.stxStack.isEmpty then return .missing else return s.stxStack.back

def getSourceInputContext {m} [Monad m] [MonadFileMap m] [MonadLog m] : m InputContext :=
  return {
    inputString := (← getFileMap).source
    fileMap     := ← getFileMap
    fileName    := ← getFileName
  }

end Lean.Parser

open Parser in
@[cleanup]
def runLintersWithCleanup : CommandElab := fun eoi =>
  -- Only run noninteractively.
  unless Elab.inServer.get (← getOptions) do
    -- profileitM Exception "linting" (← getOptions) do
    -- withTraceNode `Elab.lint (fun _ => return m!"running linters") do
    let ls ← lintersWithCleanupRef.get
    let header ← parseHeaderRaw (← getSourceInputContext)
    unless header.isMissing do -- throw error if not?
      for h : i in 0...ls.size do
        -- what if `runOnHeader`/`runOnEOI` error?
        if ← ls[i].runOnHeader then ls[i].runOn header
        IO.recordRange i header
    for h : i in 0...ls.size do
      if ← ls[i].runOnEOI then ls[i].runOn eoi
      IO.recordRange i eoi
    for h : i in 0...ls.size do
      -- Note: we only check this here (as opposed to before `recordRange`s) so that we never accidentally wait indefinitely.
      if ← ls[i].shouldCleanup then
        IO.waitForPunched! i
        ls[i].cleanup
