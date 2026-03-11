module

public import Lean
public import Skimmer.Refactor.Edit
public import Lake

open Lean

public section

/-- Exactly like `Lake.env`, but just provides the `SpawnArgs`. -/
public def Lake.envSpawnArgs.{u} {m : Type → Type u} [MonadWorkspace m] [Monad m]
    (cmd : String) (args : Array String := #[]) :
    m IO.Process.SpawnArgs := return {cmd, args, env := ← getAugmentedEnv}

/-- Exactly like `Lake.exe`, but just provides the `SpawnArgs`. Note that this does not alter the trace; see instead `fetchExeSpawnArgs` to mix the exe's trace into the current job. -/
public def Lake.exeSpawnArgs.{u} {m : Type → Type u}
    [MonadWorkspace m] [Monad m] [MonadLiftT IO m] [MonadError m]
    (name : Name) (args  : Array String := #[])
    (buildConfig : BuildConfig := {}) : m IO.Process.SpawnArgs := do
  let ws ← getWorkspace
  let some exe := ws.findLeanExe? name
    | error s!"unknown executable `{name}`"
  let exeFile ← ws.runBuild exe.fetch buildConfig
  Lake.envSpawnArgs exeFile.toString args

/-- Exactly like `Lake.exe`, but just provides the `SpawnArgs`. -/
public def Lake.fetchExeSpawnArgs
    (name : Name) (args  : Array String := #[]) : FetchM (Job IO.Process.SpawnArgs) := do
  let some exe := (← getWorkspace).findLeanExe? name
    | error s!"unknown executable `{name}`"
  (← exe.fetch).mapM (sync := true) fun exeFile =>
    Lake.envSpawnArgs exeFile.toString args

def Lake.Package.skimmerDir (pkg : Package) : System.FilePath :=
  pkg.buildDir / "skimmer"

def Lake.Package.skimmerFilePath (pkg : Package) (path : System.FilePath) (ext : String) :
    System.FilePath :=
  pkg.skimmerDir / path |>.addExtension ext

def Lake.LeanLib.skimmerDir (lib : LeanLib) : System.FilePath :=
  lib.pkg.skimmerDir / "lib_dir" / lib.name.toString

def Lake.LeanLib.skimmerFilePath (lib : LeanLib) (path : System.FilePath) (ext : String)
    : System.FilePath :=
  lib.skimmerDir / path |>.addExtension ext

namespace Lake.Module

open Skimmer

def skimmerDir (mod : Lake.Module) : System.FilePath :=
  mod.filePath mod.pkg.skimmerDir "" -- is directory-like

def skimmerFilePath (mod : Lake.Module) (path : System.FilePath) (ext : String) :
    System.FilePath :=
  mod.skimmerDir / path |>.addExtension ext

def skimmerEditsRecord (mod : Lake.Module) : System.FilePath :=
  mod.skimmerFilePath "editsrecord" "json"

end Lake.Module

namespace Skimmer

-- TODO: Is it alright to put these `System.FilePath`s in the build files? Certainly not great for caching. Hmm, what information does lake need to construct the actual filepaths? We could save that, and just always figure out the filepaths before passing into the exe. Are they relative?

-- Temporary approach: write everything to one big file so it's an "artifact"

structure EditMData where
  -- TODO: include locations
  numEdits : Nat
  numReviews : Nat
deriving ToJson, FromJson, Inhabited, Hashable, Repr

instance : EmptyCollection EditMData := ⟨⟨0,0⟩⟩

instance : Append EditMData where
  append m₀ m₁ := {
    numEdits := m₀.numEdits + m₁.numEdits
    numReviews := m₀.numReviews + m₁.numReviews
  }

/-- Currently just holds the location of all EditsRecord files. In the future, when buildArtifactUnlessUpToDate can build multiple files or we have some other intermediary, this should point to the edits-/
structure GlobalEditMData where
  arts : Array (Name × System.FilePath)
deriving ToJson, FromJson, Inhabited, Hashable

def mkGlobalEditMData (buildFiles : Array System.FilePath) (mods : Array Lake.Module) :
    GlobalEditMData where
  arts := mods.map (·.name) |>.zip buildFiles

/-- Written to Json to record edits. If present, `preview` contains the file with edits applied.
TODO: `NameMap` could get bulky, and in standard operation we'd write it many times, even when not changing it. This should be improved.

Also read from json at the start of recording edits to grab the replacements from prior imports.

In the future, these should be split out into separate build files. The obstruction currently is a matter of convenience: `buildArtifactUnlessUpToDate` only allows writing one file.
-/
structure EditsRecord where
  mdata : EditMData
  edits : Array Edit
  preview : Option String
deriving ToJson, FromJson, Inhabited, Repr

structure EditsRecordWithState α extends EditsRecord where
  state : α
deriving Inhabited

-- TODO: why can't these be derived?
instance [ToJson α] : ToJson (EditsRecordWithState α) where
  toJson x := toJson x.toEditsRecord |>.mergeObj <| Json.mkObj [("state", toJson x.state)]

instance [FromJson α] : FromJson (EditsRecordWithState α) where
  fromJson? x := do
    let toEditsRecord : EditsRecord ← fromJson? x
    let state ← x.getObjValAs? α "state"
    return { toEditsRecord, state }

def _root_.System.FilePath.writeJson (file : System.FilePath) (a : α) [ToJson α] : IO Unit := do
  Lake.createParentDirs file
  IO.FS.writeFile file (toJson a).compress

@[inline] def _root_.String.readJson? {α : Type} [FromJson α] (s : String) : Except String α := do
  fromJson? <|← Json.parse s

def _root_.System.FilePath.readJson (α) [FromJson α] (path : System.FilePath) : IO α := do
  .ofExcept <| (← IO.FS.readFile path).readJson?

def EditsRecord.readEdits (path : System.FilePath) : IO (Array Edit) :=
  (·.edits) <$> path.readJson EditsRecord

-- TODO: this will become more informative
def EditMData.ofEditsRecord (path : System.FilePath) : IO EditMData := do
  return (← path.readJson EditsRecord).mdata

def EditMData.ofGlobalEditMData (path : System.FilePath) : IO EditMData := do
  let { arts } ← path.readJson GlobalEditMData
  let mut result : EditMData := {}
  for (_, path) in arts do
    result := result ++ (← EditMData.ofEditsRecord path)
  return result

def EditsRecord.write (buildFile : System.FilePath) (e : EditsRecord) : IO Unit :=
  buildFile.writeJson e

def EditMData.write (buildFile : System.FilePath) (e : EditMData) : IO Unit := do
  buildFile.writeJson e

-- /-- Written by an `applyRefactor` facet/action. -/
-- structure EditsWrittenRecord where
--   newLeanFileHash : Option Lake.Hash

-- TODO: This is a workaround to let us jsonify what we need from `Lake.Module`s. Is there a better way...? Kind of surprised `Lake.Module`s don't jsonify.
public structure Lake.JsonModule where
  name : Name
  leanFile : System.FilePath
deriving Inhabited, ToJson, FromJson

/-- Args common to any exe. Todo: reorganize. -/
public structure ExeArgs where
  name : Name
  mod : Lake.JsonModule
  setupFile : System.FilePath
  importArts : Array System.FilePath
deriving Inhabited, ToJson, FromJson

-- Temp: one big file
/-- Computed by the lake facet orchestrating edit recording prior to recording edits, then fed to the refactor-recording process. `replacements` contains the filepaths for output artifacts (for now, `EditsRecord`s) of imports.

This is intended to be small and easy to compute, as it will be passed over json to a subprocess.

As usual, buildfile paths are synchronized by calling the same constructor on common `Lake.Module`s rather than passing the paths around.
-/
public structure RefactorArgs extends ExeArgs where
  buildFile : System.FilePath
  preview : Bool
deriving Inhabited, ToJson, FromJson

def RefactorArgs.readState (args : RefactorArgs) [FromJson α] (empty : α) (merge : α → α → α) :
    IO α := do
  if args.importArts.isEmpty then return empty else
    let mut r : α := empty
    for file in args.importArts do
      let { state .. } ← file.readJson <| EditsRecordWithState α
      r := merge r state
    return r

-- currently assumes we get all replacements we need from the direct imports
def RefactorArgs.readReplacements (args : RefactorArgs) : IO (NameMap Name) := do
  args.readState {} (·.union)

end Skimmer

namespace Lake.Module

open Skimmer

-- don't need to create parent dirs, taken care of at write time
def mkRefactorArgs (facetName : Name) (mod : Lake.Module) (setupFile : System.FilePath)
    (importArts : Array System.FilePath)
    (preview := false) :
    RefactorArgs where
  name := facetName
  mod := { name := mod.name, leanFile := mod.leanFile }
  buildFile := mod.skimmerEditsRecord
  setupFile
  importArts
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
