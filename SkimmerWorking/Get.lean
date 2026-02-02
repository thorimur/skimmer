module

public import SkimmerWorking.Cruft
public import Skimmer.Refactor.Util.Ident
import Lake
import Lake.Load.Config
public import Lake.Load.Workspace
public import SkimmerWorking.Main

open Lean Elab Command Language.Lean

def Lake.Module.getRecordedEdits (mod : Lake.Module) : IO (Array Skimmer.Edit) := do
  let json ← .ofExcept <| Json.parse (← IO.FS.readFile mod.jsonSkimmerFile)
  .ofExcept <| fromJson? json
