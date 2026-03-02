/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Skimmer.Working.LakeIO
import Batteries.Util.Pickle
public meta import Lake

open Lean

/-!
## Plans

- Interprocess communication will be used here. We want IPC that's integrated with lake, so that we can
  - write an artifact *as well as* sending it, duplicating the data
  - receive some data *or attempt to find the written version*
  This lets us pick up noninteractively. might also be necessary for rewinding? need to distinguish from git stuff.

  We can *start* with the lake version, I think.

  There's a question: what writes an artifact? I think writing artifacts is costly, and *for now*, we may as well do it per-module, following lake abstractions. In the future this might change, and we might ask for custom facet kinds.

  Let's therefore put this "lake communication" underneath a layer. The issue is we can't load the workspace in the language server, right...? So we need a way to get something out of a spawn. Let's have a "poor man's facet" for now which is capturing the stdout of a process and expecting it to be a reference to a single file, then reading that file in IO. For now we need pickle; this will be subsumed by LeanSerialize. The crucial thing here is that we can call this from within the language server. In the future, we'll receuve a ByteArray from stdout and deserialize it.

  We also want an interface between Std.Broadcast/Sync and subprocesses; maybe this is LeanGate's transport.


  We can get by with:
  - elaborating dive syntax calls out to an exe which communicates back and forth with the language server via pickle jars
    - specifically, sends aggregated metadata. should be a lake artifact. Not clear if it's a package artifact or what?

  - We have a module facet which runs refactoring then pickles it to an olean. It returns the filepath + a filepath to metadata
  - But maybe we call this module facet via lake API from an exe, so that we can aggregate over all the jobs and make our own custom reports
  - (Should isolate subprocess boundary and make entering it "correctly" convenient.)
  - Currently, the path is known to the parent process, so it can construct the facet return data without waiting for the job/actual computation. It passes the path to the job and the job doesn't need to send anything back. That's the trick. In our case we need to pickle everything (the edits, the mdata) and read it later to "send it back". Ideally we want to aggregate before we hit the language server. Not clear to me what the trace for that artifact is, but this is a detail

  - Need more dynamic, interactive options for which things get refactored. Specifically we need to aggregate all the build artifacts. So this is another sort of facet? But consider e.g. a folder, or My.Mod.Foo+. Not clear to me. Maybe the exe aggregates? Tricky part is they're not cumulative, meaning e.g. aggregates for Foo+ vs. Bar+ don't have much to do with each other. That's fine. But...where do they go? Probably some skimmer hub location that records input configs for each build...
-/

def pickleJarLid := "~~~pickleJar:"

/-- Technically both names and filepaths can contain newlines, but we assume they don't for now. -/
def System.FilePath.toPickleJar (typeName : Name) (path : System.FilePath) : String :=
  s!"{pickleJarLid}\n{typeName.toString}\n{path.normalize.toString}\n"

def String.getPickleJar (s : String) : Option (Name × System.FilePath) := do
  -- TODO: this position wrangling is a bit miserable :( will be replaced by nice IPC
  let s := s.toSlice
  let startPos ← s.find? pickleJarLid
  let s := s.sliceFrom startPos
  let nameStartPos ← s.find? "\n"
  let s := s.sliceFrom nameStartPos
  let nameEndPos ← s.find? "\n"
  let name := s.sliceTo nameEndPos |>.trimAscii.copy.toName
  let s := s.sliceFrom nameEndPos
  let fileEndPos ← s.find? "\n"
  let filePath := s.sliceTo fileEndPos |>.trimAscii.copy
  return (name, System.FilePath.mk filePath)

/-- Writes a pickle jar to stdout. -/
unsafe def sendPickleJar (path : System.FilePath) (x : α) [TypeName α]
    (key : Name := by exact decl_name%) : IO Unit := do
  pickle path x key
  IO.println <| path.toPickleJar (TypeName.typeName α)

/-- Writes a pickle jar to stdout using a temporary file. -/
unsafe def packPickleJar (x : α) [TypeName α] (key : Name := by exact decl_name%) :
    IO Unit := do
  let (_,path) ← IO.FS.createTempFile
  pickle path x key
  IO.println <| path.toPickleJar (TypeName.typeName α)

namespace IO.Process

/-- Considers success to be given by exit code 0. -/
@[inline] def Output.getSuccess? (o : Output) : Option String :=
  if o.exitCode = 0 then o.stdout else none

/-- Considers success to be given by exit code 0. Returns stdout in that case, or throws. -/
@[inline] def Output.toIO (o : Output) : IO String :=
  if o.exitCode = 0 then return o.stdout else
    throw (.userError s!"Process exited with code {o.exitCode}:\n{o.stderr}")

structure MMappedFile where
  region : CompactedRegion
  path : System.FilePath

unsafe def MMappedFile.free (m : MMappedFile) : IO Unit := do
  m.region.free
  FS.removeFile m.path

unsafe def openPickleJar (α) [TypeName α] (hasJar : String) :
    IO (α × MMappedFile) := do
  let some (name, path) := hasJar.getPickleJar
    | throw (.userError "Output did not contain a pickle jar")
  unless name = TypeName.typeName α do
    throw (.userError s!"Got type {name} from pickle jar; expected {TypeName.typeName α}")
  let (a, region) ← unpickle α path
  return (a, { region, path })

-- TODO: withConsumingPickleJar

/-- Runs `args` with input `input?` and collects its output. If it succeeds, interprets the stdout
as a filepath and tries to unpickle the data from it. Should only be used with "cooperating"
processes. Throws if pickle jar is absent or has contents of an unexpected type. -/
unsafe def runAndOpenPickleJar (α) [TypeName α]
    (args : SpawnArgs) (input? : Option String := none) :
    IO (α × MMappedFile) := do
  let out ← (← output args input?).toIO
  openPickleJar α out

-- Shouldn't do this, on windows we can't delete mmapped files apparently
-- /-- Runs `args` with input `input?` and collects its output. If it succeeds, interprets the stdout
-- as a filepath and tries to unpickle the data from it. Should only be used with "cooperating"
-- processes. Throws if pickle jar is absent or has contents of an unexpected type. -/
-- unsafe def runAndConsumePickleJar (α) [TypeName α]
--     (args : SpawnArgs) (input? : Option String := none) :
--     IO (α × CompactedRegion) := do
--   let out ← (← output args input?).toIO
--   consumePickleJar α out

namespace Skimmer

open Skimmer

public meta section

syntax Lake.tgtSpec := ("+" noWs)? ident (noWs ":" noWs ident)?
syntax Lake.pkgSpec := ("@" noWs)? ident (noWs "/" noWs (Lake.tgtSpec)?)?
syntax Lake.buildSpec := Lake.tgtSpec <|> Lake.pkgSpec

syntax (name := refactorSpecStx) "refactor " "deprecated " Lake.buildSpec+ : command

def toPartialBuildKey (stx : TSyntax ``Lake.buildSpec) : Except String Lake.PartialBuildKey := do
  let some x := stx.raw.reprint | .error s!"Could not reprint syntax:{stx}"
  Lake.PartialBuildKey.parse x

def _root_.Lake.PartialBuildKey.toHumanReadableString
    (key : Lake.PartialBuildKey) (capital := false) : String :=
  let t := if capital then "T" else "t"
  match key with
  | Lake.BuildKey.module mod => s!"{t}he module {mod}"
  | .packageModule pkg mod => s!"{t}he module {mod}{
    if pkg.isAnonymous then "" else s!" in package {pkg}"}"
  | .packageFacet pkg facet => s!"{t}he facet {facet}{
    if pkg.isAnonymous then "" else s!" in package {pkg}"}"
  | .facet tgt facet => s!"{toHumanReadableString tgt capital}, facet {facet}"
  | .packageTarget pkg tgt => s!"{t}he target {tgt}{
    if pkg.isAnonymous then "" else s!" in package {pkg}"}"
  | .package pkg => if pkg.isAnonymous then s!"{t}he current package" else s!"{t}he package {pkg}"

deriving instance BEq, Hashable for Lake.PartialBuildKey

-- TODO: just for demo purposes. env extension is the right way
meta initialize refactorTgtRef : IO.Ref (Syntax × Array Lake.PartialBuildKey) ←
  IO.mkRef (.missing, {})

elab_rules : command
| `(refactor deprecated $stx:Lake.buildSpec*) => do
  let buildKeys ← stx.mapM (ofExcept <| toPartialBuildKey ·)
  IO.Lake.checkTarget buildKeys
  refactorTgtRef.set (← getRef, buildKeys)

-- TODO: make these actions extensible by subtools, and automatically integrate them with interactive choices for the next ones. nested `?` isn't ideal. Could just use an array then check for wellformedness during elaboration
syntax (name := diveStx) "dive " ("prepare " ("execute")?)? : command

def _root_.String.andList (xs : List String) : String :=
  match xs with
  | [] => "– none –"
  | [x] => x
  | [x₀, x₁] => x₀ ++ " and " ++ x₁
  | _ => ", ".intercalate xs.dropLast ++ ", and " ++ xs.getLast!

open Lean Elab Command Meta Tactic.TryThis
elab_rules : command
| `(diveStx|dive%$tk) => do

  let (ref, keys) ← refactorTgtRef.get
  if ref.isMissing then throwError "No action registered yet."
  IO.Lake.checkTarget keys

  liftCoreM <| do
    addSuggestion tk (header := s!"Prepare the following actions?\n\n  \
          {ref.reprint.getD s!"{ref}"}\n\n\
        This will refactor {String.andList (keys.map (·.toHumanReadableString)).toList}.")
      (s := { suggestion := .string "dive\n  prepare" })
| `(command|dive%$tk prepare%$p) => do
  let (ref, keys) ← refactorTgtRef.get
  if ref.isMissing then throwError "No action registered yet."
  IO.Lake.checkTarget keys

  let mut result : Skimmer.EditMData := {}
  for key in keys do
    let path ← IO.Lake.query (.facet key `recordRefactors) System.FilePath
    -- TODO: read in the full edits here? Or laazily do so for a widget, at least
    result := result ++ (← Skimmer.EditMData.read path)
  let modules := result.modules.foldl (init := {}) NameSet.insert
  let reviewStr := if result.numReviews = 0 then "" else
    s!", {result.numReviews} of which needs review"
  -- for (mod, edit) in edits do
  --   let reviewStr := if edit.any (·.shouldReview?.isSome) then s!", {edit.countP (·.shouldReview?.isSome)} of which needs review:\n{"\n".intercalate (edit.filter (·.shouldReview?.isSome) |>.map fun { replacement, shouldReview? .. } => "  " ++ shouldReview?.get! ++ " => " ++ replacement).toList }" else "."
  --   header := s!"{header}----\n{mod}:\n\nPrepared {edit.size} refactors{reviewStr}\n"

  let mut header : String :=
    s!"Prepared {result.numEdits} refactors for {modules.size} modules{reviewStr}.\n"
  liftCoreM do
    addSuggestion (mkNullNode #[tk, p]) (header := s!"{header}\nApply refactors?") (s := { suggestion := .string "dive\n  prepare\n  execute" }) -- TODO: fix. low prio
| `(command|dive prepare execute) => do
  let (ref, keys) ← refactorTgtRef.get
  if ref.isMissing then throwError "No action registered yet."
  IO.Lake.checkTarget keys

  for key in keys do
    IO.Lake.build (.facet key `applyRefactors)
  logInfo m!"Applied refactors!\n\nPlease make a commit."
