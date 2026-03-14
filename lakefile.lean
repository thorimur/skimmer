import Lake
import Lake.CLI

-- open System Lean

open Lake DSL

package skimmer where version := v!"0.1.0"

-- require "leanprover-community" / batteries @ git "main"

@[default_target] lean_lib Skimmer where
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target] lean_exe applyTryThisExe where
  root := `Skimmer.Working.ApplyTryThis
  supportInterpreter := true
  leanOptions := #[⟨`experimental.module, true⟩]

open Lean hiding Module

/-- Copy-pasted from Lake.Build.Module for now; apparently lakefiles can't import private scopes by being modules? -/
private partial def fetchTransImportArts
  (directImports : Array ModuleImport) (directArts : NameMap ImportArtifacts) (nonModule : Bool)
: FetchM (NameMap ImportArtifacts) := do
  let q ← directImports.foldlM (init := #[]) fun q imp => do
    let some mod := imp.module? | return q
    let input ← (← mod.input.fetch).await
    let importAll := strictOr nonModule imp.importAll
    return enqueue importAll input q
  walk directArts q
where
  walk s q := do
    if h : 0 < q.size then
      let (mod, importAll) := q.back
      let q := q.pop
      if let some arts := s.find? mod.name then
        -- may need to promote a module system `import` to an `import all`
        -- size of 1 = non-module, 3 = module system `import`, 4 = `import all`
        unless importAll && arts.size == 3 do
          return ← walk s q
      let info ← (← mod.exportInfo.fetch).await
      let arts := if importAll then info.allArts else info.arts
      let s := s.insert mod.name arts
      let input ← (← mod.input.fetch).await
      let q := enqueue importAll input q
      walk s q
    else
      return s
  enqueue importAll input q :=
    input.imports.foldr (init := q) fun imp q =>
      if let some mod := imp.module? then
        if importAll || imp.isExported then
          q.push (mod, nonModule || (importAll && imp.importAll))
        else q
      else q

/-- `leanArts` writes a setup file that contains all transitive imports, and in that way differs slightly from what the `setup` facet gives. However, this file is "temporary" in that it is not added to the trace, so the artifacts we get from the cache don't include setup files, and `leanArts` can succeed with no `setupFile` present.

We could be cleverer about this, recreating the trace and all. Instead, for maximal robustness, we just fetch leanArts to ensure everything is up to date, then recompute. (We could check that it exists first.)
-/
module_facet setupWithTrans (mod) : ModuleSetup := do
  (← mod.leanArts.fetch).bindM fun _ => do -- maybe writes setupFile to disk
    (← mod.setup.fetch).mapM fun setup => do
      let directImports := (← (← mod.input.fetch).await).imports
      let transImpArts ← fetchTransImportArts directImports setup.importArts !setup.isModule
      return {setup with importArts := transImpArts}

abbrev Lake.Module.setupWithTrans (mod : Lake.Module) : BuildInfo :=
  mod.facet `setupWithTrans

module_facet setupWithTransPersistent (mod) : System.FilePath := do
  (← mod.setupWithTrans.fetch).mapM fun setup => do
    let file := mod.setupFile
    createParentDirs file
    IO.FS.writeFile file (toJson setup).pretty
    return file

-- TODO: dot notation for custom module_facets when :/

-- TODO: can we disable memoization?

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

inline_modules Skimmer.Refactor.Lake

-- TODO: we may want instead to stick to general `FetchM` functions.

/-- This fetches `facetName` for every import satisfying `filter`, then runs `shadow` on the result, passing in the modules satisfying filter and the setup.

Passes in the filepath for `setup.json`, including transitive imports as in `buildLean`.

TODO: split out that bit about the setup?

TODO: don't pass along to `shadow`, just fetch again?

TODO: leave filtering logic to the facet...?

TODO: group `Module` with `α`?

TODO: automatically infer `facetName` at elaboration time via `decl_name%`? -/
@[inline] def recFetchShadowingBuildWhere (mod : Module) (fetchFn : Module → FetchM (Job α))
    (shadow : System.FilePath → Array Module → Array α → FetchM (Job α))
    (filter : Option (Module → FetchM Bool) := none) :
    FetchM (Job α) := do
  let setupFile ← fetch <| mod.facet `setupWithTransPersistent
  let imports ← (← mod.imports.fetch).await -- correct?
  let imports ← if let some filter := filter then imports.filterM filter else pure imports
  setupFile.bindM fun setupFile => do
    let shadowImported := Job.collectArray <|← imports.mapM fun mod => fetchFn mod
    shadowImported.bindM fun shadowImported => shadow setupFile imports shadowImported

def recFetchFacetShadowingBuildWhere (mod : Module) (facetName : Name)
    [∀ mod : Module, FamilyOut BuildData (mod.facet facetName).key α] -- TODO: better way?
    (shadow : System.FilePath → Array Module → Array α → FetchM (Job α))
    (filter : Option (Module → FetchM Bool) := none) :
    FetchM (Job α) :=
  recFetchShadowingBuildWhere mod (fetch <| ·.facet facetName) shadow filter

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

-- TODO: noramlize for filepaths
def mkSkimmerMDataFileName (facetName : Name) := s!"editsmdata_{facetName}"

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

@[inline] def Lake.Module.fetchRefactorWithExeSpawnArgs
    (recordRefactorFacet refactorExe : Name) (setupFile : System.FilePath)
    (importArts : Array System.FilePath)
    (mod : Lake.Module) :
    FetchM (Skimmer.RefactorArgs × Job (IO.Process.SpawnArgs)) := do
  let leanJob ← mod.lean.fetch
  discard leanJob.await
  addTrace leanJob.getTrace
  let args := mod.mkRefactorArgs recordRefactorFacet setupFile importArts
  return (args, ← fetchExeSpawnArgs refactorExe #[(toJson args).compress])

def refactorWithExe
    (args : Skimmer.RefactorArgs) (job : Job (IO.Process.SpawnArgs)) :
    FetchM (Job System.FilePath) := do
  -- let leanJob ← mod.lean.fetch
  -- discard leanJob.await
  -- addTrace leanJob.getTrace
  -- let args := mod.mkRefactorArgs recordRefactorFacet setupFile importArts
  -- let spawnArgs ← fetchExeSpawnArgs refactorExe #[(toJson args).compress]
  job.mapM fun spawnArgs => do
    discard <| buildArtifactUnlessUpToDate (text := true) args.buildFile do
      discard <| captureProc spawnArgs
    return args.buildFile -- TODO: correct?

-- def Lake.Module.refactorWithExe
--     (recordRefactorFacet refactorExe : Name)
--     (setupFile : System.FilePath)
--     (importArts : Array System.FilePath) (mod : Lake.Module) :
--     FetchM (Job System.FilePath) := do
--   -- let leanJob ← mod.lean.fetch
--   -- discard leanJob.await
--   -- addTrace leanJob.getTrace
--   -- let args := mod.mkRefactorArgs recordRefactorFacet setupFile importArts
--   -- let spawnArgs ← fetchExeSpawnArgs refactorExe #[(toJson args).compress]
--   let (args, job) ← mod.fetchRefactorWithExeSpawnArgs recordRefactorFacet refactorExe setupFile importArts
--   job.mapM fun spawnArgs => do
--     discard <| buildArtifactUnlessUpToDate (text := true) args.buildFile do
--       discard <| captureProc spawnArgs
--     return args.buildFile -- TODO: correct?

open Skimmer

-- TODO: check to make sure errors in leanArts make the whole thing fail?
-- TODO: does this handle traces correctly?
module_facet recordCurrentTryThisRefactors (mod) : Option System.FilePath := do
  let (args, exeJob) ← mod.fetchRefactorWithExeSpawnArgs `recordCurrentTryThisRefactors `applyTryThisExe mod.setupFile #[]
  (← fetch <| mod.facet `setupWithTransPersistent).bindM fun _ => do
    let shouldAttempt :=
      match ← readTraceFile mod.traceFile with
      | .ok t => t.log.hasEntries
      | _ => true
    unless shouldAttempt do return Job.pure none
    let job ← refactorWithExe args exeJob
    return job.map some

library_facet recordCurrentTryThisRefactors (lib) : System.FilePath := do
  (← lib.modules.fetch).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod =>
      fetch <| mod.facet `recordCurrentTryThisRefactors
    buildFiles.mapM fun buildFiles => do
      let file := lib.skimmerFilePath "editmdata_trythis" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

package_facet recordCurrentTryThisRefactors (pkg) : System.FilePath := do
  (← fetch <| pkg.facet `libModules).bindM fun mods => do
    let buildFiles := Job.collectArray <|← mods.mapM fun mod =>
      fetch <| mod.facet `recordCurrentTryThisRefactors
    buildFiles.mapM fun buildFiles => do
      let file := pkg.skimmerFilePath "editmdata_trythis" "json"
      discard <| buildArtifactUnlessUpToDate file do
        file.writeJson (mkGlobalEditMData buildFiles mods)
      return file

-- Noninteractive for now; also records try this edits.
module_facet applyCurrentTryThis (mod) : Option System.FilePath := do
  let recordPath ← fetch <| mod.facet `recordCurrentTryThisRefactors
  recordPath.mapM fun recordPath => do
    let some recordPath := recordPath | return none
    let edits ← EditsRecord.readEdits recordPath
    unless edits.isEmpty do
      -- TODO: lock file?
      let src ← IO.FS.readFile mod.leanFile
      IO.FS.writeFile mod.leanFile <| src.applyEdits edits
    return some recordPath

def applyCurrentTryThisAux (mods : Array Module) : FetchM (Job <| Array (Name × Nat)) := do
  let job := Job.collectArray <|← mods.mapM fun mod => fetch <| mod.facet `recordCurrentTryThisRefactors
  job.mapM fun recordPaths => do
    let mut acc := #[]
    for mod in mods, recordPath? in recordPaths do
      let some recordPath := recordPath? | continue
      let { mdata, edits, .. } ← recordPath.readJson EditsRecord
      unless edits.isEmpty do
        -- TODO: lock file?
        let src ← IO.FS.readFile mod.leanFile
        IO.FS.writeFile mod.leanFile <| src.applyEdits edits
        acc := acc.push (mod.name, mdata.numEdits)
    return acc

library_facet applyCurrentTryThis (lib) : Array (Name × Nat) := do
  (← lib.modules.fetch).bindM (applyCurrentTryThisAux ·)

package_facet applyCurrentTryThis (pkg) : Array (Name × Nat) := do
  (← fetch <| pkg.facet `libModules).bindM (applyCurrentTryThisAux ·)
