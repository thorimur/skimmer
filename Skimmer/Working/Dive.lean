
import Lean
import Skimmer.Working.Main
import Skimmer.Working.Get

namespace Skimmer

open Lean

initialize refactorLibRef : IO.Ref NameSet ← IO.mkRef {}

syntax (name := refactorSpecStx) "refactor " "deprecated " ident : command

elab_rules : command
| `(refactor deprecated $i:ident) => refactorLibRef.modify (·.insert i.getId)

syntax (name := diveStx) "dive " ("prepare " ("execute")?)? : command

open Lean Elab Command Meta Tactic.TryThis
elab_rules : command
| `(diveStx|dive%$tk) => do
  -- let ws ← IO.loadWorkspace
  -- for lib in ws.root.leanLibs do
  --   if (← refactorLibRef.get).contains lib.name then
  --     let mods ← lib.getModuleArray
  -- TEMP: IO.loadWorkspace crashes the server.
  let lib := `WorkingTest
  let mods := #[`WorkingTest.Test, `WorkingTest.ReviewTest]


  liftCoreM <| do
    addSuggestion tk (header := s!"Prepare the following actions?\n\n  refactor deprecated {lib}\n\nThis will refactor the following modules:\n  {mods.toList}") (s := { suggestion := .string "dive\n  prepare" })
| `(command|dive%$tk prepare%$p) => do
  -- let ws ← IO.loadWorkspace
  -- for lib in ws.root.leanLibs do
  --   if (← refactorLibRef.get).contains lib.name then
      let lib'name := `WorkingTest
      let toBuildFile s : System.FilePath := ".lake" / "build" /"lib" /"lean"/ "WorkingTest" / s!"{s}.json.skimmed"
      let modSuffixes := #[`Test, `ReviewTest]
      let e ← IO.Process.run {
        cmd := "lake"
        args := #["exe", exeName, lib'name.toString]
      }


      let mut edits := #[]
      for mod in modSuffixes do
        edits := edits.push (`WorkingTest ++ mod, ← getRecordedEdits (toBuildFile mod))
      let mut header : String := s!"Prepared refactors for {edits.size} modules.\n"
      for (mod, edit) in edits do
        let reviewStr := if edit.any (·.shouldReview?.isSome) then s!", {edit.countP (·.shouldReview?.isSome)} of which needs review:\n{"\n".intercalate (edit.filter (·.shouldReview?.isSome) |>.map fun { replacement, shouldReview? .. } => "  " ++ shouldReview?.get! ++ " => " ++ replacement).toList }" else "."
        header := s!"{header}----\n{mod}:\n\nPrepared {edit.size} refactors{reviewStr}\n"


      liftCoreM do
        addSuggestion (mkNullNode #[tk, p]) (header := s!"{header}\nApply refactors?") (s := { suggestion := .string "dive\n  prepare\n  execute" })
| `(command|dive prepare execute) => do
  -- let ws ← IO.loadWorkspace
  -- for lib in ws.root.leanLibs do
  --   if (← refactorLibRef.get).contains lib.name then
    -- let lib'name := `WorkingTest
    let toBuildFile s : System.FilePath := ".lake" / "build" /"lib" /"lean"/ "WorkingTest" / s!"{s}.json.skimmed"
    let modSuffixes := #[`Test, `ReviewTest]
    for mod in modSuffixes do
      let edits ← getRecordedEdits (toBuildFile mod)
      let source ← IO.FS.readFile ("WorkingTest" / s!"{mod.toString}.lean")
      IO.FS.writeFile ("WorkingTest" / s!"{mod.toString}.lean") (source.applyEdits edits)
      IO.FS.writeFile (toBuildFile mod) ""
      logInfo m!"Wrote {edits.size} edits to {mod}."
