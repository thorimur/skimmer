module

public import Skimmer.Working.Cruft
public import Skimmer.Refactor.Util.Ident
public import Lake
import Lake.Load.Config
public import Lake.Load.Workspace

def sourceFileDummy := r#"
import Lean
import Batteries.Tactic.Alias

#check Bool.true

def Bar := Bool

@[deprecated Bar (since := "yesterday")] alias Foo := Bar

def Baz := Foo

def Foo.not (b : Foo) := Bool.not b

def Foo.notnot (b : Foo) := b.not.not

def Int.flipIf (b : Foo) (i : Int) : Int :=
  bif b then -i else i

@[deprecated Int.flipIf (since := "yesterday")]
def Foo.flipIf (b : Foo) (i : Int) : Int := i.flipIf

example (b : Foo) : Int := b.flipIf (-3 : Int)

#check Foo
"#

-- deriving instance Repr for PackageConfig
-- deriving instance Repr for Package
-- deriving instance Repr for Workspace


-- import Lean
-- import Batteries.Tactic.Alias

open Lean Elab Command Language.Lean

-- bundle functionality in `IO.refactorDeprecated (snap : CommandParsedSnapshot) : IO (NameMap Name, Array Edit)`. This should get the `Command.State` I suppose? ah, maybe we need functionality to use the previous Command.State? Depends on whether we want to start before each command or after. I think it's got to be after, right?

-- Anyway, it should runCommandElabM on the `snap`, with `refactorDeprecated (stx) (infotree?) : CommandElabM (NameMap Name × Array Edit)`.

-- This is how Lean.Language.Process constructs the `Command.Context`.
-- `read` is in `LeanProcessingM` which is just above `ProcessingM` which seems to have context that just extends `inputContext` and nothing else?

-- might want more narrow arguments, at least for now.
-- by the way, is ictx from somewhere else (too)? the header snap?
def Lean.Language.Lean.CommandParsedSnapshot.toCommandCtx (ictx : Parser.InputContext) (snap : CommandParsedSnapshot) : Command.Context :=
  let stx := snap.getSyntax -- gets from infotrees, suboptimal. maybe feed in or work in a monad in future where it's cached
  -- TODO: could we get more from command context in infotrees?
  { ictx with
    ref := stx
    cmdPos := stx.getPos?.getD ⟨0⟩ -- why not snap.getPos ???? 0 for everything but terminal command
    snap? := none /- TODO should probably populate in future -/
    cancelTk? := none /- TODO from snap.elabSnap or snap.elabSnap.elabSnap?? or?? -/
  }

variable (x : EIO Exception Bool)

-- TODO: should build on top of this to grab messages and such, I think that's what runAndReport does? would runAndReport fill in syntax/pos?

def Lean.Language.Lean.CommandParsedSnapshot.EIO.runCommandElabM (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : EIO Exception (α × State) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run (snap.getState)

def Lean.Language.Lean.CommandParsedSnapshot.EIO.runCommandElabM' (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : EIO Exception α := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run' (snap.getState)

def Lean.Language.Lean.CommandParsedSnapshot.runCommandElabM (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : IO (Except Exception (α × State)) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run (snap.getState) |>.toIO'

def Lean.Language.Lean.CommandParsedSnapshot.runCommandElabM' (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : IO (Except Exception α) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run' (snap.getState) |>.toIO'


-- <restore> #check Lean.Language.Lean.process
-- Seems we pass parserState forward. Not sure why it doesn't seem to make it into the relevant command snaps `parserState.pos` fields.
/-
    let ctx ← read
    let scope := cmdState.scopes.head!
    -- reset per-command state
    let cmdStateRef ← IO.mkRef { cmdState with
      messages := .empty, traceState := {}, snapshotTasks := #[] }
    let cmdCtx : Elab.Command.Context := { ctx with
      cmdPos       := beginPos
      snap?        := if internal.cmdlineSnapshots.get scope.opts then none else snap
      cancelTk?    := some cancelTk
    }
-/

public def _root_.Lake.Module.oleanSkimmerFile (mod : Lake.Module) : System.FilePath :=
  mod.leanLibPath "olean.skimmed"

public def _root_.Lake.Module.jsonSkimmerFile (mod : Lake.Module) : System.FilePath :=
  mod.leanLibPath "json.skimmed"

public def exeName := "working"

deriving instance ToJson for String.Pos.Raw, Syntax.Range, Skimmer.Edit
deriving instance FromJson for String.Pos.Raw, Syntax.Range, Skimmer.Edit

-- Given a `usage : Syntax`, we need to get the info from the infotree of *the part that the ident looks at* for the expected type. This depends I think. Then we get the expected type, make replacements, see if it all works out.

def _root_.String.Pos.Raw.rangeAt (pos : String.Pos.Raw) : Syntax.Range := ⟨pos, pos⟩

open Skimmer

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

public structure EditMData where
  -- TODO: include locations
  numEdits : Nat
  numReviews : Nat
deriving ToJson, FromJson, Inhabited, Hashable

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




-- Alternate, temporary approach: write everything to one big file so it's an "artifact"

public structure EditsRecord where
  mdata : EditMData
  edits : Array Edit
  replacements : NameMap Name
  preview : Option String
deriving Inhabited, ToJson, FromJson

def EditsRecord.write (buildFile : System.FilePath) (e : EditsRecord) : IO Unit := do
  Lake.createParentDirs buildFile
  IO.FS.writeFile buildFile (toJson e).compress

-- TODO: understand this comment in `fetchOleanCore`:
/-
      /-
      Avoid recompiling unchanged OLean files.
      OLean files transitively include their imports.
      THowever, imports are pre-resolved by Lake, so they are not included in their trace.
      -/
      newTrace s!"{mod.name.toString}:{facet}"

-/


-- TODO: it's unfortunate that `buildArtifactUnlessUpToDate` limits us to a single file. We'd like to keep these separate.

-- TODO: (major) We could builk up `Edit` to `DeprecationEdit`, which includes extra data like `review` status. Then refactoring just collapses it down to normal edits. The thing, of course, is that we want *persistent* access to this metadata. And we want ways to handle it.
-- So we need to *serialize the bulky thing*, and have a way of *registering* this refactor with the overall edit system. This needs to provide (1) any special ways to disply this metadata during the interface (2) an instance of how to transform these into edits. sorting the edits should happena all at once. however, we *do* need meta-handling if there are conflicts. (would it be nice to write down the resolution in the dive file? make merge conflicts first class a la jj?)

-- TODO: make monadic. honestly giving exes access to the lake workspace would be great. or maybe I just want non-lakefile scripts?
-- instance : Repr Language.Lean.CommandParsedSnapshot where
--   reprPrec snap _ := s!"{snap.desc}: [{snap.stx}] {snap.elabSnap.elabSnap.get}"

-- Is this the right way to do things, or should we be computing the `EditsArtifact`?

#check Lake.buildArtifactUnlessUpToDate

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

-- def RefactorArgs.readReplacements (args : RefactorArgs) : IO (NameMap Name) := do
--   if args.replacements.isEmpty then return {} else
--     let mut r : NameMap Name := {}
--     for file in args.replacements do
--       let more : NameMap Name ← .ofExcept <| fromJson? <|← IO.FS.readFile file
--       r := r.union more
--     return r

end LakefileSync

-- currently assumes we get all we need from the direct imports
def RefactorArgs.readReplacements (args : RefactorArgs) : IO (NameMap Name) := do
  if args.replacements.isEmpty then return {} else
    let mut r : NameMap Name := {}
    for file in args.replacements do
      let more : NameMap Name ← .ofExcept <| fromJson? <|← IO.FS.readFile file
      r := r.union more
    return r


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


-- (What not to do) what if we returned the metadata and sent it back along stdout? Then made it a facet value?
-- I suppose the issue is that it is no longer an artifact we can read. We have to run the lake facet to get it.
public def refactor (args : RefactorArgs) : IO Unit := do
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile args.mod.leanFile
  let inputCtx := Parser.mkInputContext source args.mod.name.toString -- TODO check if correct
  let (setup, snap) ← Skimmer.runFrontend inputCtx { mainModuleName := args.mod.name }
  -- IO.println setup.result!.get.imports
  let some { headerParserState, headerState, commands } := snap.toCommandSnaps
    | IO.eprintln "Could not find snaps."
  let some r := setup.result?.get | IO.eprintln "Could not find setup."
    -- turn imports into skimmer build filepaths (do it the basic way for now)
  -- spawn a `lake exe working` on them if they don't exist (lake will do this in the future)
  -- read into `replacements`.
  -- IO.println s!"{repr r.stx.raw.getRangeWithTrailing?}; {headerParserState.pos}"
  let mut replacements : NameMap Name ← args.readReplacements
  let mut edits : Array Edit := #[] -- import actual `Edit` functionality here
  for snap in commands do
    -- TODO: none of these capture the error where the date and identifier are flipped. What does?
    -- if snap.isFatal then
    --   IO.eprintln s!"Fatal snap {snap.isFatal}"
    -- if snap.parserState.recovering then
    --   IO.eprintln s!"Parser recovering" -- not convinced this will ever be populated
    -- if snap.getState.messages.hasErrors then
    --   IO.eprintln s!"Errors:\n{← snap.getState.messages.toArray.mapM (·.toString)}"
    -- TODO: could be useful to run in new state, but this is really a subprocess-version problem.
    -- IO.println s!"++++\nrunning snap at '{snap.getSyntax.reprint!.take 30}...'"
    match ← snap.runCommandElabM' inputCtx <| refactorDeprecated.post replacements edits with
    | .error ex => IO.eprintln (← ex.toMessageData.toString)
    | .ok (replacements', edits') =>
      replacements := replacements'
      edits := edits'
    -- IO.println s!"edits: {repr edits}\n{snap.getSyntax.reprint.getD "couldn't reprint"}"
  -- finally write olean.skimmed. don't bother with error handling yet
  -- TODO standardize edits postprocessing as part of what "edits" are. this should be an extensible part of introducing accumulation
  if edits.any (·.shouldReview?.isSome) then
    edits := edits.push ⟨headerParserState.pos.rangeAt, "\nimport Skimmer.Working.Review\n\n", none⟩
  -- IO.println (edits.map (repr ·.range))
  edits := edits.qsortOrd
  let mdata : EditMData := {
    numEdits := edits.size
    numReviews := edits.countP (·.shouldReview?.isSome) }
  -- IO.println s!"====\nedits: {← (toMessageData edits).toString}"
  -- -- IO.println s!"====\n{sourceFileDummy.applyEdits edits}"

  -- IO.println s!"====\n{source.applyEdits edits}"

  -- replaceDeprecated (r : NameMap Name) (e : Array String) :=
  --   return (r, e.push s!"another! (foo exists: {(← getEnv).find? `foo |>.isSome})")
  -- TODO: store replacements in build file for extra things
  -- IO.FS. mod.jsonSkimmerFile

  -- discard <| art.write edits replacements mdata source

  let editsRecord : EditsRecord := {
    mdata,
    edits,
    replacements,
    preview := if args.preview then some (source.applyEdits edits) else none
  }
  editsRecord.write args.buildFile

/-
Rewrite write-edits:

possibly just get json. otherwise

get module, modules, etc. Assume we have olean

rewrite `importModules` for `importSkimmerModules` or something? not clear when this should and shouldn't follow regular imports?

in any case just assume we have the olean paths. this is a lake thing so let's cruft it. `ls` maybe and just read every olean.skimmed lol. Still requires `readModuleData` or something.

though...these would normally be in environment extensions which require subprocesses to set up...so...

let's just use json for everything right now?

ToJson, FromJson, and after FromJson, write as usual using paths.


-/


-- def getTopologicallySortedModulesAux (ws : Lake.Workspace) (mod : Lake.Module) (acc : Array Lake.Module) : Lake.Module :=
--   let

-- open Lake System in
-- /- temporary before moving to Lake, written by Codex -/
-- public def IO.loadWorkspace (root : FilePath := ".") : IO Workspace := do
--   let (elan?, lean?, lake?) ← findInstall?
--   let some lean := lean? | throw <| IO.userError "Lean install not found"
--   let some lake := lake? | throw <| IO.userError "Lake install not found"
--   let env ← (Env.compute lake lean elan? none).toIO .userError
--   let cfg : LoadConfig := {
--     lakeEnv := env
--     wsDir := root
--     relPkgDir := "."
--     relConfigFile := "lakefile.lean"
--   }
--   let some ws ← (Lake.loadWorkspace cfg).toBaseIO | throw <| IO.userError "workspace load failed"
--   return ws

-- currently we expect the module to be fed in via `mod`, and the `EditsArtifact` to be fed in
public def main (args : List String) : IO Unit := do
  match args with
  | [refactorArgs] => do refactor (← .ofExcept <| fromJson? refactorArgs)
  | _ => throw (.userError "Expected json for refactor args")
