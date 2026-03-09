import Lake
import Lake.CLI

-- open System Lean

open Lake DSL

package skimmer where version := v!"0.1.0"

require "leanprover-community" / batteries @ git "main"

@[default_target] lean_lib Skimmer where leanOptions := #[⟨`experimental.module, true⟩]

-- @[default_target] lean_lib SkimmerPlugin where
--   globs := #[`SkimmerPlugin.+]
--   defaultFacets := #[`lean_lib.shared]
--   leanOptions := #[⟨`experimental.module, true⟩]

-- @[default_target] lean_lib SkimmerTest where
--   globs := #[`SkimmerTest.+]
--   leanOptions := #[⟨`experimental.module, true⟩]

-- @[default_target] lean_lib SkimmerExtra where
--   globs := #[`SkimmerExtra.+]
--   leanOptions := #[⟨`experimental.module, true⟩]

-- @[default_target] lean_lib SkimmerHub where
--   globs := #[`SkimmerExtra.+]
--   leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe write_edits where
  root := `Skimmer.Execute
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe refactorDeprecatedExe where
  root := `Skimmer.Working.RefactorDeprecated
  supportInterpreter := true
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe applyTryThisExe where
  root := `Skimmer.Working.ApplyTryThis
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

namespace Inline

open Lean Parser Elab Term Command

/-- `replaceAllSourceInfo ref cmd` replaces all source info in `cmd` with that of `ref`, if it
exists (or leaves `cmd` alone). -/
partial def replaceAllSourceInfo (ref cmd : Syntax) : Syntax :=
  if let some info := ref.getInfo? then
    cmd.setInfo info |>.modifyArgs (·.map <| replaceAllSourceInfo ref)
  else cmd

partial def parseAndElabAux (ictx : InputContext) (ctx : ParserModuleContext)
    (s : ModuleParserState) (log : MessageLog) (ref : Syntax) (mod : Name) : CommandElabM Unit := do
  let (cmd, s, log) := parseCommand ictx ctx s log
  if log.hasErrors then
    modify fun s => { s with messages := s.messages ++ log } -- TODO: check that this is right
    throwError "[{mod}] Failed to parse command:\
      {indentD (cmd.unsetTrailing.reprint.getD <| toString cmd)}"
  if isTerminalCommand cmd then return
  elabCommand (replaceAllSourceInfo ref cmd) -- not `*TopLevel`, don't need linters etc.
  modify fun s => { s with infoState := {} } -- don't reset messages
  -- TODO: wait for messages?
  if ← MonadLog.hasErrors then
    throwError "[{mod}] Failed to elaborate command:\
      {indentD (cmd.unsetTrailing.reprint.getD <| toString cmd)}" -- TODO: not firing
  -- TODO: get `log`?
  let ctx : ParserModuleContext := {
      env := ← getEnv
      options := ← getOptions
      openDecls := ← getOpenDecls
      currNamespace := ← getCurrNamespace }
  parseAndElabAux ictx ctx s log ref mod

partial def elabModule (ref : Syntax) (mod : Name) (processedModules : NameSet) :
    CommandElabM NameSet := if processedModules.contains mod then return processedModules else do
  let mut file := modToFilePath "." mod "lean"
  unless ← file.pathExists do
    -- TODO: not all packages use the default location for dependencies, necessarily.
    -- the principled thing is to get this from the root somehow
    file := modToFilePath ("." / ".lake" / "packages" / "skimmer") mod "lean"
    unless ← file.pathExists do
    -- TODO: could also look in lake packages
      throwError "Could not locate file {file}.\ncurrent directory: {← IO.currentDir}"
  let src ← IO.FS.readFile file -- TODO: command-click on `mod`
  let ictx := mkInputContext src file.toString
  let (header, s, log) ← parseHeader ictx
  if log.hasErrors then
    modify fun s => { s with messages := s.messages ++ log }
    throwError "Failed to parse header."
  let `(Module.header| $[module%$modTk?]? $[prelude]? $imports*) := header
    | throwUnsupportedSyntax
  let mut processedModules := processedModules.insert mod
  for imp in imports do
    let `(Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $mod) := imp
      | throwUnsupportedSyntax
    let mod := mod.getId
    match mod.getRoot with
    | `Lean | `Std | `Lake => continue
    | _ =>
      if processedModules.contains mod then continue
      processedModules ← elabModule ref mod processedModules
  -- TODO: reset the rest of the Command.State except for important things, consider changing mainModule, context, etc.
  -- TODO: refactor?
  let scopes ← getScopes
  modify fun s => { s with scopes := [{ header := "", opts := {} }] }
  let ctx : ParserModuleContext := { env := ← getEnv, options := {} }
  let infoState ← getInfoState
  parseAndElabAux ictx ctx s log ref mod
  modify fun s => { s with infoState, scopes }
  return processedModules

-- TODO: command-click for modules listed
-- TODO: go-to-"real"-def on constants, somehow
/-- Inlines the module into the lakefile. Also inlines transitive imports (except for core imports, which are already available); includes all private scopes. Resets namespaces before and after. -/
elab "inline_modules " mods:Parser.ident+ : command => do
  let mut processedModules := {}
  for mod in mods do
    processedModules ← withRef mod do
      elabModule mod mod.getId processedModules

end Inline

inline_modules Skimmer.Refactor.Lake Skimmer.LakeSerialized

-- TODO: write this to a json file somewhere
target workspace : Serialized.Workspace := do
  let ws ← getWorkspace
  return Job.pure ws.toSerializedWorkspace

target facetNames : Array Name := do
  let facetCfgs := (← getWorkspace).facetConfigs.toArray.map (·.fst)
    |>.filter (!(`default).isSuffixOf ·)
    |>.qsort (·.lt)
  return Job.pure facetCfgs

target libraries (pkg) : Array Name := do
  return Job.pure <| pkg.leanLibs.map (·.name) |>.qsort Name.lt

target targetNames (pkg) : Array Name := do
  return Job.pure <| (pkg.targetDecls.map (·.name)).qsort Name.lt

script checkTarget (args) do
  discard <| parseTargetSpecs (← getWorkspace) args |>.toIO fun cliError => cliError.toString
  IO.Process.exit 0

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

/-
What does lake need to know? It needs to know
(1) the name.
(2) the output type; we can standardize this, probably.
(3) what should be mixed into traces


Possibly, multiple refactors should be temporarily registered in lake as some single combo facet? Not clear. Possibly we want to aggregate all edit mdatas.

We want a way of registering a refactor that somehow aggregates the mdata...

We also want the mdata aggregated in advance into a single file, unlike now.

Also not sure how competing refactors should work. One at a time?
-/


private def getEscapedNameParts? (acc : List String) : Name → Option (List String)
  | Name.anonymous => if acc.isEmpty then none else some acc
  | Name.str n s => do
    let s ← Name.escapePart s
    getEscapedNameParts? (s::acc) n
  | Name.num _ _ => none

def mkNameLit? (n : Ident) : Option NameLit :=
  let info := n.raw.getInfo?.getD .none
  getEscapedNameParts? [] n.getId  |>.map fun ss =>
    Syntax.mkNameLit ("`" ++ ".".intercalate ss) info

-- TODO: noramlize for filepaths
def mkSkimmerMDataFileName (facetName : Name) := s!"editsmdata_{facetName}"

/-- A temporary affordance to allow producing multiple facets. In the future, this will be subsumed
by driving lake builds. Note that this version means that each build job runs totally
indepdendently. -/
macro "refactor_facets" facetNames:ident+ : command => do
  let cmds ← facetNames.flatMapM fun facetName => do
    let some nameLit := mkNameLit? facetName | Macro.throwUnsupported
    return #[
      ← `(command|
        module_facet $facetName:ident (mod) : System.FilePath := do
          recFetchFacetShadowingBuildWhere mod $nameLit
            (filter := some fun i => return i.pkg == mod.pkg)
            fun _ _ importArts => do
              (← mod.lean.fetch).mapM fun _ => do -- mix lean file into trace
                let args := mod.mkRefactorArgs $nameLit importArts
                discard <| buildArtifactUnlessUpToDate (text := true) args.buildFile do
                  discard <| captureProc <|← Lake.fetchExeSpawnArgs `working #[args.json.compress]
                return args.buildFile -- TODO: correct?
      ),
      ← `(command|
        library_facet $facetName:ident (lib) : System.FilePath := do
          (← lib.modules.fetch).bindM fun mods => do
            let buildFiles := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet $nameLit
            buildFiles.mapM fun buildFiles => do
              let file := lib.skimmerFilePath (mkSkimmerMDataFileName $nameLit) "json"
              discard <| buildArtifactUnlessUpToDate file do
                file.writeJson (lib.mkSkimmerMData $nameLit buildFiles mods)
              return file
      ),
      ← `(command|
        package_facet $facetName:ident (pkg) : System.FilePath := do
          let aamods := Job.collectArray (← pkg.leanLibs.mapM (·.modules.fetch))
          aamods.bindM fun aamods => do
            -- TODO: abstract out into package_facet modules
            let mut modset : ModuleSet := {}
            let mut mods := #[]
            for amods in aamods do
              for mod in amods do
                unless modset.contains mod do
                  mods := mods.push mod
                  modset := modset.insert mod
            let buildFiles := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet $nameLit
            buildFiles.mapM fun buildFiles => do
              let file := pkg.skimmerFilePath (mkSkimmerMDataFileName $nameLit) "json"
              discard <| buildArtifactUnlessUpToDate file do
                file.writeJson (pkg.mkSkimmerMData $nameLit buildFiles mods)
              return file
      )
    ]
  return ⟨mkNullNode cmds⟩

/-- Gets a (deduplicated) array of modules in the package's libraries. -/
package_facet libModules (pkg) : Array Module := do
  let aamods := Job.collectArray (← pkg.leanLibs.mapM (·.modules.fetch))
  aamods.mapM fun aamods => do
    let mut modset : ModuleSet := {}
    let mut mods := #[]
    for amods in aamods do
      for mod in amods do
        unless modset.contains mod do
          mods := mods.push mod
          modset := modset.insert mod
    return mods

def Lake.Module.refactorWithExe (recordRefactorFacet refactorExe : Name)
    (importArts : Array System.FilePath) (mod : Lake.Module) :
    FetchM (Job System.FilePath) := do
  (← mod.lean.fetch).bindM fun _ => do -- mix lean file into trace
    let args := mod.mkRefactorArgs recordRefactorFacet importArts
    (← fetchExeSpawnArgs refactorExe #[(toJson args).compress]).mapM fun spawnArgs => do
      discard <| buildArtifactUnlessUpToDate (text := true) args.buildFile do
        discard <| captureProc spawnArgs
      return args.buildFile -- TODO: correct?

-- TODO(NOW): create a standard `FetchM` wrapper for processes, passing them filepaths, and an `IO` wrapper for other `IO` actions which passes in filepaths appropriately...

-- TODO(NOW): also read/write from these filepaths? use buildartifact unless up to date?
-- TODO(NOW): where does `buildArtifactUnlessUpToDate` come in?

-- TODO: would be much better if we could buildArtifactsUnlessUpToDate.
module_facet recordRefactors (mod) : System.FilePath := do
  recFetchFacetShadowingBuildWhere mod `recordRefactors
    (filter := some fun i => return i.pkg == mod.pkg)
    fun _ _ replacementPaths =>
      mod.refactorWithExe `recordRefactors `refactorDeprecatedExe replacementPaths

open Skimmer

library_facet recordRefactors (lib) : System.FilePath := do
  (← lib.modules.fetch).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `recordRefactors
    buildFiles.mapM fun buildFiles => do
      let file := lib.skimmerFilePath "editmdata" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

package_facet recordRefactors (pkg) : System.FilePath := do
  (← fetch <| pkg.facet `libModules).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `recordRefactors
    buildFiles.mapM fun buildFiles => do
      let file := pkg.skimmerFilePath "editmdata" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

-- TODO: record the trace or hash in the recorded edits. Invalidate if it doesn't match the lean file hash.
-- TODO: better return value. Right now it returns the filepath. We may call out into something more interactive here.
module_facet applyRefactors (mod) : System.FilePath := do
  -- Note: this only works by relying on `buildArtifactUnlessUpToDate`.
  -- We do check things twice, which is unfortunate, but no big deal.
  let isUpToDate ← (← getWorkspace).checkNoBuild <| fetch <| mod.facet `recordRefactors
  unless isUpToDate do
    -- TODO: better error? should we error at all, or return something useful?
    error s!"Recorded refactors for {mod} are not up-to-date."
  let recordPath ← fetch <| mod.facet `recordRefactors
  recordPath.mapM fun recordPath => do
    -- TODO(NOW): we need to check if edits have been applied yet. Technically, this might happen while trying to fetch the recorded edits? Not clear.
    let edits ← EditsRecord.readEdits recordPath
    unless edits.isEmpty do
      -- TODO: lock file?
      let src ← IO.FS.readFile mod.leanFile
      IO.FS.writeFile mod.leanFile <| src.applyEdits edits
    return recordPath

library_facet applyRefactors (lib) : Array System.FilePath := do
  (← lib.modules.fetch).bindM fun mods => do
    return Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `applyRefactors

package_facet applyRefactors (pkg) : Array System.FilePath := do
  (← fetch <| pkg.facet `libModules).bindM fun mods =>
    return Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `applyRefactors

-- TODO: ensure `leanArts` doesn't replay, there's no need for this
module_facet recordTryThisRefactors (mod) : System.FilePath := do
  (← mod.leanArts.fetch).bindM fun _ =>
    mod.refactorWithExe `recordTryThisRefactors `applyTryThisExe #[]

library_facet recordTryThisRefactors (lib) : System.FilePath := do
  (← lib.modules.fetch).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod =>
      fetch <| mod.facet `recordTryThisRefactors
    buildFiles.mapM fun buildFiles => do
      let file := lib.skimmerFilePath "editmdata_trythis" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

package_facet recordTryThisRefactors (pkg) : System.FilePath := do
  (← fetch <| pkg.facet `libModules).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod =>
      fetch <| mod.facet `recordTryThisRefactors
    buildFiles.mapM fun buildFiles => do
      let file := pkg.skimmerFilePath "editmdata_trythis" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

-- Noninteractive for now; also records try this edits.
module_facet applyTryThis (mod) : System.FilePath := do
  let recordPath ← fetch <| mod.facet `recordTryThisRefactors
  recordPath.mapM fun recordPath => do
    let edits ← EditsRecord.readEdits recordPath
    unless edits.isEmpty do
      -- TODO: lock file?
      let src ← IO.FS.readFile mod.leanFile
      IO.FS.writeFile mod.leanFile <| src.applyEdits edits
    return recordPath

def applyTryThisAux (mods : Array Module) : FetchM (Job <| Array (Name × Nat)) := do
  let job := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `recordTryThisRefactors
  job.mapM fun recordPaths => do
    let mut acc := #[]
    for mod in mods, recordPath in recordPaths do
      let { mdata, edits, .. } ← recordPath.readJson EditsRecord
      unless edits.isEmpty do
        -- TODO: lock file?
        let src ← IO.FS.readFile mod.leanFile
        IO.FS.writeFile mod.leanFile <| src.applyEdits edits
        acc := acc.push (mod.name, mdata.numEdits)
    return acc

library_facet applyTryThis (lib) : Array (Name × Nat) := do
  (← lib.modules.fetch).bindM (applyTryThisAux ·)

package_facet applyTryThis (pkg) : Array (Name × Nat) := do
  (← fetch <| pkg.facet `libModules).bindM (applyTryThisAux ·)
