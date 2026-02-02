
import Lean
import Skimmer.Working.Main

namespace Skimmer

open Lean

initialize refactorLibRef : IO.Ref NameSet ← IO.mkRef {}

syntax (name := refactorSpecStx) "refactor " "deprecated " ident : command

elab_rules : command
| `(refactor deprecated $i:ident) => refactorLibRef.modify (·.insert i.getId)

syntax (name := diveStx) "dive " ("prepare " ("apply ")?)? : command


#check findSysroot
elab_rules : command
| `(diveStx|dive) => do
  let ws ← IO.loadWorkspace
  for lib in ws.root.leanLibs do
    if (← refactorLibRef.get).contains lib.name then
      let mods ← lib.getModuleArray

  let libs ← refacto
