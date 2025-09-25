/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Skimmer.Cleanup.Elab
import Skimmer.LinterWithCleanup.Defs

open Lean Elab Command

-- TODO: make async?
/--
Only to be used when running linters with cleanup manually, outside of `runLinters`. Replicates loop of `runLinters`.

Does *not* update the `rangeRecordsRef`.
-/
protected def CommandElab.runAsLinter (run : CommandElab) (stx : Syntax) (linterName : Name): CommandElabM Unit := do
  withTraceNode `Elab.lint (fun _ => return m!"running linter: {.ofConstName linterName}")
      (tag := linterName.toString) do
    let savedState ← get
    try
      run stx
    catch ex =>
      match ex with
      | Exception.error ref msg =>
        logException (.error ref m!"linter {.ofConstName linterName} failed: {msg}")
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

def parseHeaderRawWithLeadingWhitespace (inputCtx : InputContext) : IO (Substring × Syntax) := do
  let dummyEnv ← mkEmptyEnvironment
  let tokens := Module.updateTokens (getTokenTable dummyEnv)
  letI run (p : ParserFn) (s : ParserState) := p.run inputCtx { env := dummyEnv, options := {} } tokens s
  let ws := run whitespace (mkParserState inputCtx.inputString)
  let whitespaceSubstring := inputCtx.substring 0 ws.pos
  if ws.hasError then return (whitespaceSubstring, .missing) else
  let s := run Module.header.fn ws
  let stx := if s.stxStack.isEmpty then .missing else s.stxStack.back
  return (whitespaceSubstring, stx)

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
    let (ws, header) ← parseHeaderRawWithLeadingWhitespace (← getSourceInputContext)
    unless header.isMissing do -- throw error if not?
      for h : i in 0...ls.size do
        -- what if `runOnHeader`/`runOnEOI` error?
        if let some run := ls[i].runOnHeader then
          CommandElab.runAsLinter (run ws) header ls[i].name
        recordRange i header (isHeader := true)
    for h : i in 0...ls.size do
      if ← ls[i].runOnEOI then
        CommandElab.runAsLinter ls[i].run eoi ls[i].name
      recordRange i eoi
    for h : i in 0...ls.size do
      -- Note: we only check this here (as opposed to before `recordRange`s) so that we never accidentally wait indefinitely.
      if ← ls[i].shouldCleanup then
        IO.waitUntilPunched! i
        ls[i].cleanup
