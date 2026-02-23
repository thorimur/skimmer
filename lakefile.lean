import Lake

-- open System Lean

open Lake DSL

package skimmer where version := v!"0.1.0"

require "leanprover-community" / batteries @ git "main"
require "leanprover" / "doc-gen4" @ git "main"


@[default_target] lean_lib Skimmer where leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerPlugin where
  globs := #[`SkimmerPlugin.+]
  defaultFacets := #[`lean_lib.shared]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerTest where
  globs := #[`SkimmerTest.+]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerExtra where
  globs := #[`SkimmerExtra.+]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_lib SkimmerHub where
  globs := #[`SkimmerExtra.+]
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe write_edits where
  root := `Skimmer.Execute
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe working where
  root := `Skimmer.Working.Main
  supportInterpreter := true
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib WorkingTest where
  globs := #[`WorkingTest.+]
  leanOptions := #[⟨`experimental.module, true⟩]

section

open Lean

structure EditData where
  edits : System.FilePath
  mdata : System.FilePath
  -- The following have to be pickled into the mdata, in order to cross the subprocess boundary
  -- The artifact consists of both of these together, of course. Can we have subartifacts?
  -- Further on we may want edits to be contributed to by multiple things; will we want to aggregate the mdata on the fly? Probably produce an aggregated mdata via pickle
  -- uri : Lsp.DocumentUri
  -- editLocs   : Array Lsp.Range
  -- reviewLocs : Array Lsp.Range

end

open Lean hiding Module

/-- Waits for the setup file to exist before returning it. -/
module_facet setupWithTransFile (mod) : System.FilePath := do
  (← mod.leanArts.fetch).mapM fun _ => -- writes setupFile to disk
    return mod.setupFile

-- TODO: dot notation for custom module_facets when :/

-- TODO: can we disable memoization?

/--
Gets the `ModuleSetup`, but reads from the setup file to provide the `ModuleSetup` with `ModuleArtifacts` populated with all transitive import artifacts, not just direct ones.

TODO: this should really be done a different way?

TODO: withRegisterJob? maybeRegister?
-/
module_facet setupWithTrans (mod) : ModuleSetup := do
  (← fetch <| mod.facet `setupWithTransFile).mapM fun file => do -- writes setupFile to disk
    let arts ← ModuleSetup.load file
    IO.println s!"{arts.importArts.toArray.map (·.1)}"
    return arts

abbrev Lake.Module.setupWithTrans (mod : Lake.Module) := mod.facet `setupWithTrans

-- TODO: we may want instead to stick to general `FetchM` functions.

/-- This fetches `facetName` for every import satisfying `filter`, then runs `shadow` on the result, passing in the modules satisfying filter and the setup.

If `transImportArts := true`, populates the `ModuleSetup.importArts` with all transitive imports. Currently we wait for the module to be built if we want to get the transitive artifacts; we could extract this from lake if we wanted.

TODO: take in a `ModuleSetup` instead of having a flag?

TODO: don't pass along to `shadow`, just fetch again?

TODO: leave filtering logic to the facet...?

TODO: group `Module` with `α`?

TODO: automatically infer `facetName` at elaboration time via `decl_name%`? -/
@[inline] def recFetchShadowingBuildWhere (mod : Module) (fetch : Module → FetchM (Job α))
    (shadow : ModuleSetup → Array Module → Array α → FetchM (Job α))
    (filter : Option (Module → FetchM Bool) := none) (transImportArts := false) :
    FetchM (Job α) := do
  let setup ← if transImportArts then mod.setupWithTrans.fetch else mod.setup.fetch
  let imports ← (← mod.imports.fetch).await
  let imports ← if let some filter := filter then imports.filterM filter else pure imports
  setup.bindM fun setup => do
    let shadowImported := Job.collectArray <|← imports.mapM fun mod => fetch mod
    shadowImported.bindM fun shadowImported => shadow setup imports shadowImported

def recFetchFacetShadowingBuildWhere (mod : Module) (facetName : Name)
    [∀ mod : Module, FamilyOut BuildData (mod.facet facetName).key α] -- TODO: better way?
    (shadow : ModuleSetup → Array Module → Array α → FetchM (Job α))
    (filter : Option (Module → FetchM Bool) := none) (transImportArts := false) :
    FetchM (Job α) :=
  recFetchShadowingBuildWhere mod (fetch <| ·.facet facetName) shadow filter transImportArts

/-- Note that the current package is not necessarily set for a bare module facet. -/
def Lake.Module.inCurrPackage.{u} {m : Type → Type u} [Monad m] [MonadReaderOf CurrPackage m]
    (mod : Module) : m Bool :=
  return (← getCurrPackage?).isEqSome mod.pkg

/-- Note that the current package is not necessarily set for a bare module facet. -/
def Lake.Module.inRootPackage.{u} {m : Type → Type u} [Monad m] [MonadWorkspace m]
    (mod : Module) : m Bool :=
  return (← getRootPackage) == mod.pkg

-- TODO(NOW): create a standard `FetchM` wrapper for processes, passing them filepaths, and an `IO` wrapper for other `IO` actions which passes in filepaths appropriately...

-- TODO(NOW): also read/write from these filepaths? use buildartifact unless up to date?
-- TODO(NOW): where does `buildArtifactUnlessUpToDate` come in?

-- TODO: unfortunate that we can't Jsonify the module
section LakefileSync

-- TODO: unfortunate that we can't Jsonify the module
public structure Lake.JsonModule where
  name : Name
  leanFile : System.FilePath
deriving Inhabited, ToJson, FromJson

-- Temp: one big file
public structure RefactorArgs where
  mod : Lake.JsonModule
  replacements : Array System.FilePath
  buildFile : System.FilePath
  preview : Bool
deriving Inhabited, ToJson, FromJson

def Lake.Module.skimmerLibPath (mod : Lake.Module) (ext : String) : System.FilePath :=
  if ext.isEmpty then mod.leanLibPath ext else mod.leanLibPath s!"skimmer.{ext}"

-- don't need to create parent dirs, taken care of at write time
def mkRefactorArgs (mod : Lake.Module) (replacements : Array System.FilePath)
    (preview := false) : RefactorArgs :=
  {
    mod := { mod with leanFile := mod.leanFile },
    buildFile := mod.skimmerLibPath "editrecord.json"
    replacements
    preview
  }

end LakefileSync

-- TODO: would be much better if we could buildArtifactsUnlessUpToDate.
module_facet refactor (mod) : System.FilePath := do
  recFetchFacetShadowingBuildWhere mod `refactor (filter := some fun i => return i.pkg == mod.pkg)
    fun _ _ replacementPaths => do
      let args := mkRefactorArgs mod replacementPaths
      discard <| buildArtifactUnlessUpToDate (text := true) args.buildFile do
        discard <| captureProc { -- todo: check using correct proc
          cmd := "lake"
          args := #["exe", "working", (toJson args).compress]
        }
      return Job.pure args.buildFile

-- library_facet refactor (lib) : System.FilePath := do
--   (← lib.modules.fetch).bindM fun mods => do
--     let mods := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `refactor
--     -- TODO: read the mdata from the files, then aggregate into a single file.
--     -- A bit difficult, since it requires duplicating the Lean definitions in the lakefile.
--     -- Could also drive this in an exe to accommodate other collections of modules. Or have new targets that represent these, where the modules given are arguments/env variables


-- module_facet pickleJar (mod : Module) : Unit := do
--   recFetchShadowingBuildWhere mod `pickleJar (filter := some (·.inRootPackage)) fun _ mods _ => do
--     IO.println s!"{mod}: {← mods.mapM fun mod => return (mod, ← mod.inRootPackage)}"
--     return Job.pure ()
  -- let job ← mod.importArts.fetch
  -- job.mapM fun a => IO.println s!"{a.importArts.toArray.map fun (a, b) => a}"
  -- let job ← mod.imports.fetch
  -- job.mapM fun is => do
  --   for i in is do

  -- let job ← mod.transImports.fetch

  -- job.mapM fun j => IO.println s!"{j}"
