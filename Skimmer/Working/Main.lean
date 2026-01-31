module

import Skimmer.Working.Cruft

def sourceFileDummy := "\
import Lean

def foo : Bool := Bool.true

#check foo"

open Lean

public def main : IO Unit := do
  initSearchPath (← findSysroot)
  let inputCtx := Parser.mkInputContext sourceFileDummy "<dummy>"
  let (setup, snap) ← Skimmer.runFrontend inputCtx `Dummy
  let some { headerParserState, headerState, commands } := snap.toCommandSnaps
    | IO.eprintln "Could not find snaps."
  let some r := setup.result?.get | IO.eprintln "Could not find setup."
  IO.println s!"{repr r.stx.raw.getRangeWithTrailing?}; {headerParserState.pos}"
  for snap in commands do
    IO.println s!"----\n{snap.getSyntax.reprint.getD "couldn't reprint"}"
