/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Refactor.Edit
public import Skimmer.AttrUtil
public import Skimmer.Refactor.Init

@[expose] public section

open Lean Skimmer Command

@[inline] def Lean.Environment.getModuleName (env : Environment) (idx : Nat) :
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
  let editss := editExt.getImportedEntries env
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
  let sourceDir ← getDirOfModule (← getSrcSearchPath) `Skimmer
  let editss := editExt.getImportedEntries env
  for h : idx in [:editss.size] do
    let edits := editss[idx]
    unless edits.isEmpty do
      let some mod := env.getModuleName idx | continue
      if mod.getRoot != root || mod == env.mainModule then continue
      let path := modToFilePath sourceDir mod "lean"
      -- Mario's code:
      IO.println s!"writing {edits.size} edits to {mod} @ {path}:"
      let text ← IO.FS.readFile path
      let mut out : String := ""
      let mut prevEndPos : text.Pos := text.startPos
      for edit in edits do -- note: already sorted
        let some slice := edit.range.toSliceOf? text | continue -- TODO: trace/error
        if h : prevEndPos ≤ slice.startInclusive then
          out := out ++ {
            str := text
            startInclusive := prevEndPos
            endExclusive := slice.startInclusive
            startInclusive_le_endExclusive := h : String.Slice }
          out := out ++ edit.replacement
          prevEndPos := slice.endExclusive
        -- TODO: trace/error if not
      out := out ++ text.sliceFrom prevEndPos
      IO.println <| s!"-----\n" ++ out ++ s!"-----"
      -- IO.FS.writeFile path out
