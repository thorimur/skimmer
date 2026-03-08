/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Working.Cruft
public import Skimmer.Refactor.Edit
public import Skimmer.Refactor.Lake

open Lean Elab Command

namespace Lean.Language.Lean.CommandParsedSnapshot

-- bundle functionality in `IO.refactorDeprecated (snap : CommandParsedSnapshot) : IO (NameMap Name, Array Edit)`. This should get the `Command.State` I suppose? ah, maybe we need functionality to use the previous Command.State? Depends on whether we want to start before each command or after. I think it's got to be after, right?

-- Anyway, it should runCommandElabM on the `snap`, with `refactorDeprecated (stx) (infotree?) : CommandElabM (NameMap Name × Array Edit)`.

-- This is how Lean.Language.Process constructs the `Command.Context`.
-- `read` is in `LeanProcessingM` which is just above `ProcessingM` which seems to have context that just extends `inputContext` and nothing else?

-- might want more narrow arguments, at least for now.
-- by the way, is ictx from somewhere else (too)? the header snap?
def toCommandCtx (ictx : Parser.InputContext) (snap : CommandParsedSnapshot) : Command.Context :=
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


def EIO.runCommandElabM (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : EIO Exception (α × State) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run (snap.getState)

def EIO.runCommandElabM' (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : EIO Exception α := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run' (snap.getState)

def runCommandElabM (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : IO (Except Exception (α × State)) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run (snap.getState) |>.toIO'

def runCommandElabM' (ictx : Parser.InputContext)
    (x : Syntax → CommandElabM α) (snap : CommandParsedSnapshot) : IO (Except Exception α) := do
  x snap.getSyntax |>.run (snap.toCommandCtx ictx) |>.run' (snap.getState) |>.toIO'

end Lean.Language.Lean.CommandParsedSnapshot

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

public def exeName := "working"

-- Given a `usage : Syntax`, we need to get the info from the infotree of *the part that the ident looks at* for the expected type. This depends I think. Then we get the expected type, make replacements, see if it all works out.

def String.Pos.Raw.rangeAt (pos : String.Pos.Raw) : Syntax.Range := ⟨pos, pos⟩

open Skimmer

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

@[inline] def Skimmer.RefactorArgs.init (args : RefactorArgs) :
    IO (Parser.InputContext × ImportsSetup × Language.Lean.InitialSnapshot) := do
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile args.mod.leanFile
  let inputCtx := Parser.mkInputContext source args.mod.name.toString -- TODO check if correct
  let (setup, snap) ← Skimmer.runFrontend inputCtx { mainModuleName := args.mod.name }
  -- IO.println setup.result!.get.imports
  let some setup := setup.result?.get | throw <| .userError "Could not find setup."
  return (inputCtx, setup, snap)

@[inline] def Lean.Language.Lean.InitialSnapshot.getCommandSnaps (snap : Language.Lean.InitialSnapshot) :
    IO Language.Lean.CommandSnaps := do
  snap.toCommandSnaps.getDM (throw <| .userError "Could not find snaps.")

def Skimmer.Edit.postprocess (newImportPosition : String.Pos.Raw) (edits : Array Edit) :
    Array Edit := Id.run do
  let edits :=
    if edits.any (·.shouldReview?.isSome) then
      edits.push ⟨newImportPosition.rangeAt, "\nimport Skimmer.Working.Review\n\n", none⟩
    else edits
  return edits.qsortOrd

-- performance?
def runRefactor₂ {α} {β}
    (inputCtx : Parser.InputContext)
    (commands : Array Language.Lean.CommandParsedSnapshot)
    (init : α) (init' : β)
    (f : α → β → Syntax → CommandElabM (α × β)) : IO (α × β) := do
  let mut a : α := init
  let mut b : β := init'
  for snap in commands do
    match ← snap.runCommandElabM' inputCtx <| f a b with
    | .error ex => IO.eprintln (← ex.toMessageData.toString)
    | .ok (a', b') => a := a'; b := b'
  return (a, b)

-- TODO: we can do this async

def runRefactor
    (inputCtx : Parser.InputContext)
    (commands : Array Language.Lean.CommandParsedSnapshot)
    (init : α)
    (f : α → Syntax → CommandElabM α) : IO α := do
  let mut a : α := init -- import actual `Edit` functionality here
  for snap in commands do
    match ← snap.runCommandElabM' inputCtx <| f a with
    | .error ex => IO.eprintln (← ex.toMessageData.toString)
    | .ok a' => a := a'
  return a

def Skimmer.EditsRecordWithState.ofEdits
    (source : String) (state : α) (edits : Array Edit) (preview := false):
    EditsRecordWithState α where
  mdata := {
    numEdits := edits.size
    numReviews := edits.countP (·.shouldReview?.isSome) }
  edits
  state
  preview := if preview then some (source.applyEdits edits) else none

def Skimmer.EditsRecord.ofEdits
    (source : String) (edits : Array Edit) (preview := false) :
    EditsRecord where
  mdata := {
    numEdits := edits.size
    numReviews := edits.countP (·.shouldReview?.isSome) }
  edits
  preview := if preview then some (source.applyEdits edits) else none

def Skimmer.RefactorArgs.writeEditsRecordWithState (args : RefactorArgs)
    (source : String) (state : α) (edits : Array Edit) :
    IO Unit := do
  EditsRecordWithState.ofEdits source state edits args.preview |>.write args.buildFile

def Skimmer.RefactorArgs.writeEditsRecord (args : RefactorArgs)
    (source : String) (edits : Array Edit) :
    IO Unit := do
  EditsRecord.ofEdits source edits args.preview |>.write args.buildFile

-- (What not to do) what if we returned the metadata and sent it back along stdout? Then made it a facet value?
-- I suppose the issue is that it is no longer an artifact we can read. We have to run the lake facet to get it.
public def refactorWithState (args : RefactorArgs) (init : α)
    (f : α → Array Edit → Syntax → CommandElabM (α × Array Edit)) : IO Unit := do
  initSearchPath (← findSysroot)
  let (inputCtx, _, snap) ← args.init
  let { headerParserState, commands .. } ← snap.getCommandSnaps
  let (state, edits) ← runRefactor₂ inputCtx commands init #[] f
  args.writeEditsRecordWithState inputCtx.inputString state <|
    Edit.postprocess headerParserState.pos edits

public def refactor (args : RefactorArgs)
    (f : Array Edit → Syntax → CommandElabM (Array Edit)) : IO Unit := do
  initSearchPath (← findSysroot)
  let (inputCtx, _, snap) ← args.init
  let { headerParserState, commands .. } ← snap.getCommandSnaps
  let edits := Edit.postprocess headerParserState.pos <|← runRefactor inputCtx commands #[] f
  args.writeEditsRecord inputCtx.inputString edits

public nonrec def IO.Main.refactorWithState {α} (args : List String) (init : RefactorArgs → IO α)
  (f : α → Array Edit → Syntax → CommandElabM (α × Array Edit)) : IO Unit :=
  match args with
  | [refactorArgs] => do
    let args ← .ofExcept refactorArgs.readJson?
    refactorWithState args (← init args) f
  | _ => throw (.userError "Expected json for refactor args")

public nonrec def IO.Main.refactor (args : List String)
  (f : Array Edit → Syntax → CommandElabM (Array Edit)) : IO Unit :=
  match args with
  | [refactorArgs] => do
    let args ← .ofExcept refactorArgs.readJson?
    refactor args f
  | _ => throw (.userError "Expected json for refactor args")
