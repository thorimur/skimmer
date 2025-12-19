module


import SkimmerTest.AccumulativeLinterTest.Deprecated.Test
import Skimmer.Extension
public import Lean.Elab.Command
public meta import Skimmer.AttrUtil
public meta import Skimmer.Refactor.Edit

open Lean
local elab "#show_edits_demo" : command => do
  if Elab.inServer.get (← getOptions) then return
  let env ← getEnv
  let some idx := env.getModuleIdx? `SkimmerTest.AccumulativeLinterTest.Deprecated.Test
    | throwError "Couldn't find module"
  let edits := editExt.getModuleEntries env idx
  let file ← IO.FS.readFile "/Users/thomas/LeanContribution/skimmer/SkimmerTest/AccumulativeLinterTest/Deprecated/Test.lean"

  let newFile := file.applyEdits edits
  -- logInfo m!"{newFile}"
  IO.FS.writeFile "/Users/thomas/LeanContribution/skimmer/SkimmerTest/AccumulativeLinterTest/Deprecated/Test.lean" newFile

#show_edits_demo
