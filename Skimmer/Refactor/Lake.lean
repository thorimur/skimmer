module

public import Lean
public import Skimmer.Refactor.Edit
public import Lake

open Lean

public section

namespace Skimmer

-- Temporary approach: write everything to one big file so it's an "artifact"

structure EditMData where
  -- TODO: include locations
  numEdits : Nat
  numReviews : Nat
deriving ToJson, FromJson, Inhabited, Hashable

/-- Written to Json to record edits. If present, `preview` contains the file with edits applied.
TODO: `NameMap` could get bulky, and in standard operation we'd write it many times, even when not changing it. This should be improved.

Also read from json at the start of recording edits to grab the replacements from prior imports.

In the future, these should be split out into separate build files. The obstruction currently is a matter of convenience: `buildArtifactUnlessUpToDate` only allows writing one file.
-/
structure EditsRecord where
  mdata : EditMData
  edits : Array Edit
  replacements : NameMap Name
  preview : Option String
deriving ToJson, FromJson, Inhabited

def EditsRecord.write (buildFile : System.FilePath) (e : EditsRecord) : IO Unit := do
  Lake.createParentDirs buildFile
  IO.FS.writeFile buildFile (toJson e).compress

def _root_.System.FilePath.readJson (α) [FromJson α] (path : System.FilePath) : IO α := do
  .ofExcept <| fromJson? (← IO.FS.readFile path)

def EditsRecord.readEdits (path : System.FilePath) : IO (Array Edit) :=
  (·.edits) <$> path.readJson EditsRecord

-- TODO: This is a workaround to let us jsonify what we need from `Lake.Module`s. Is there a better way...? Kind of surprised `Lake.Module`s don't jsonify.
public structure Lake.JsonModule where
  name : Name
  leanFile : System.FilePath
deriving Inhabited, ToJson, FromJson

-- Temp: one big file
/-- Computed by the lake facet orchestrating edit recording prior to recording edits, then fed to the refactor-recording process. `replacements` contains the filepaths for output artifacts (for now, `EditsRecord`s) of imports.

This is intended to be small and easy to compute, as it will be passed over json to a subprocess.

As usual, buildfile paths are synchronized by calling the same constructor on common `Lake.Module`s rather than passing the paths around.
-/
public structure RefactorArgs where
  mod : Lake.JsonModule
  replacements : Array System.FilePath
  buildFile : System.FilePath
  preview : Bool
deriving Inhabited, ToJson, FromJson

-- currently assumes we get all replacements we need from the direct imports
def RefactorArgs.readReplacements (args : RefactorArgs) : IO (NameMap Name) := do
  if args.replacements.isEmpty then return {} else
    let mut r : NameMap Name := {}
    for file in args.replacements do
      let more : NameMap Name ← .ofExcept <| fromJson? <|← IO.FS.readFile file
      r := r.union more
    return r

end Skimmer

namespace Lake.Module

open Skimmer

def skimmerLibPath (mod : Lake.Module) (ext : String) : System.FilePath :=
  if ext.isEmpty then mod.leanLibPath ext else mod.leanLibPath s!"skimmer.{ext}"

-- don't need to create parent dirs, taken care of at write time
def mkRefactorArgs (mod : Lake.Module) (replacements : Array System.FilePath) (preview := false) :
    RefactorArgs where
  mod := { name := mod.name, leanFile := mod.leanFile }
  buildFile := mod.skimmerLibPath "editrecord.json"
  replacements
  preview

end Lake.Module

section future

/-
public structure EditsArtifact where
  replacements : Option System.FilePath
  edits : System.FilePath
  preview : Option System.FilePath
  mdataPath : System.FilePath
deriving Inhabited, ToJson, FromJson, BEq, Hashable

def EditsArtifact.readEdits (e : EditsArtifact) : IO (Array Edit) := do
  .ofExcept <| fromJson? (← IO.FS.readFile e.edits)

def EditsArtifact.writeEdits (edits : Array Edit) (e : EditsArtifact) : IO Unit :=
  IO.FS.writeFile e.edits (toJson edits).compress

-- TODO: for now we write every replacements to a file, where replacements are cumulative(!).
-- This is not at all performant, as we likely duplicate lots of data.
-- We do have to make it past the subprocess boundary, but we can just write *new* replacements to stdout, and return those as a *facet value*, then pass them back in via args.
-- There is a chance that these replacements get too big. In which case we'd want to use a file anyway. But still, only the

def EditsArtifact.readReplacements (e : EditsArtifact) : IO (NameMap Name) := do
  let some r := e.replacements | return {}
  .ofExcept <| fromJson? (← IO.FS.readFile r)

def EditsArtifact.writeReplacements (replacements : NameMap Name) (e : EditsArtifact) :
    IO Bool := do
  if replacements.isEmpty then return false else
    IO.FS.writeFile e.edits (toJson replacements).compress
    return true

def EditsArtifact.readMData (e : EditsArtifact) : IO EditMData := do
  .ofExcept <| fromJson? (← IO.FS.readFile e.edits)

def EditsArtifact.writeMData (mdata : EditMData) (e : EditsArtifact) : IO Unit :=
  IO.FS.writeFile e.edits (toJson mdata).compress

def EditsArtifact.readPreview (e : EditsArtifact) : IO (Option String) := do
 e.preview.mapM IO.FS.readFile

-- TODO: don't write preview for unchanged files
def EditsArtifact.writePreview (source : String) (edits : Array Edit)
    (e : EditsArtifact) : IO Bool := do
  let some preview := e.preview | return false
  IO.FS.writeFile preview (source.applyEdits edits)
  return true

def EditsArtifact.writePreviewAndReturn (source : String) (edits : Array Edit)
    (e : EditsArtifact) : IO (Option String) := do
  e.preview.mapM fun preview => do
    let result := source.applyEdits edits
    IO.FS.writeFile preview result; return result

def EditsArtifact.write (edits : Array Edit) (replacements : NameMap Name) (mdata : EditMData) (source : String)
    (e : EditsArtifact) : IO Unit := do
  e.writeEdits edits
  e.writeMData mdata
  discard <| e.writeReplacements replacements
  discard <| e.writePreview source edits

def Lake.creatingParentDirs (path : System.FilePath) : IO System.FilePath :=
  do Lake.createParentDirs path; return path

def mkEditsArtifact (mod : Lake.Module) (preview := true) : IO EditsArtifact := do
  let replacements ← Lake.creatingParentDirs <| mod.skimmerLibPath "replacements.json"
  let edits ← Lake.creatingParentDirs <| mod.skimmerLibPath "edits.json"
  let preview ← if preview then
    some <$> (Lake.creatingParentDirs <| mod.skimmerLibPath "preview.json") else pure none
  let mdataPath ← Lake.creatingParentDirs <| mod.skimmerLibPath "editMData.json"
  return {
    replacements,
    edits,
    preview,
    mdataPath
  }
-/
