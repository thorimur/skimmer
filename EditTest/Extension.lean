import EditTest.Edit

open Lean

initialize editExt : PersistentEnvExtension Edit (List Edit) (List Edit) ←
  registerPersistentEnvExtension {
    mkInitial       := pure {}
    addImportedFn   := fun _ _ => pure {}
    addEntryFn      := fun edits es => es ++ edits
    exportEntriesFn := fun edits => edits.toArray.sortEdits
    statsFn         := fun s => "edits added: " ++ f!"{repr s}"
    asyncMode       := .sync -- hmm
    replay?         := none
  }

@[inline] private def Lean.Environment.getModuleName (env : Environment) (idx : Nat) :
    Option Name := env.header.modules[idx]?.map (·.module)

-- From Mathlib.Tactic.Core:
/-- Returns the root directory which contains the package root file, e.g. `Mathlib.lean`. -/
def getPackageDir (pkg : String) : IO System.FilePath := do
  let sp ← getSrcSearchPath
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension "lean").pathExists
  if let some root := root? then return root
  throw <| IO.userError s!"Could not find {pkg} directory. \
    Make sure the LEAN_SRC_PATH environment variable is set correctly."
-- end Mathlib.Tactic.Core

-- From CacheM.mathlibDepPath
def getDirOfModule (sp : SearchPath) (mod : Name) : IO System.FilePath := do
  let modSourceFile ← Lean.findLean sp mod
  let some modSourceDir ← pure modSourceFile.parent
    | throw <| IO.userError s!"{mod} not found on search path:\n  {sp}"
  return modSourceDir

def executeEdits (env : Environment) (root : Name) : IO Unit := do
  let sourceDir ← getDirOfModule (← getSrcSearchPath) root
  let editss := (editExt.toEnvExtension.getState env).importedEntries
  for h : idx in [:editss.size] do
    let edits := editss[idx]
    unless edits.isEmpty do
      let some mod := env.getModuleName idx | continue
      if mod.getRoot != root || mod == env.mainModule then continue
      let path := modToFilePath sourceDir mod "lean"
      IO.println
        s!"writing {edits.size} edit{if edits.size == 1 then "" else "s"} to {mod} @ {path}"
      let text ← IO.FS.readFile path
      let out := text.applyEdits edits
      IO.FS.writeFile path out

def showEdits (env : Environment) (root : Name) : IO Unit := do
  -- let base ← Mathlib.getPackageDir "Mathlib"
  let sourceDir ← getDirOfModule (← getSrcSearchPath) `EditTest
  let editss := (editExt.toEnvExtension.getState env).importedEntries
  for h : idx in [:editss.size] do
    let edits := editss[idx]
    unless edits.isEmpty do
      let some mod := env.getModuleName idx | continue
      if mod.getRoot != root || mod == env.mainModule then continue
      let path := modToFilePath sourceDir mod "lean"
      -- Mario's code:
      IO.println s!"writing {edits.size} edits to {mod} @ {path}:"
      let text ← IO.FS.readFile path
      let mut pos : String.Pos := 0
      let mut out : String := ""
      for edit in edits do -- already sorted
        if pos ≤ edit.range.start then
          out := out ++ text.extract pos edit.range.start ++ edit.replacement
          pos := edit.range.stop
      out := out ++ text.extract pos text.endPos
      IO.println <| s!"-----\n" ++ out ++ s!"-----"
      -- IO.FS.writeFile path out
