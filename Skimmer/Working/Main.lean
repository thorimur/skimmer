module

import Skimmer.Working.Cruft
import Skimmer.Refactor.Util.Ident

def sourceFileDummy := r#"
import Lean
import Batteries.Tactic.Alias

#check Bool.true

def Bar := Bool

@[deprecated Bar (since := "yesterday")] alias Foo := Bar

def Baz := Foo

def Foo.not (b : Foo) := Bool.not b

def Foo.notnot (b : Foo) := b.not.not

#check Foo"#



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


#check Lean.Language.Lean.process
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

-- Given a `usage : Syntax`, we need to get the info from the infotree of *the part that the ident looks at* for the expected type. This depends I think. Then we get the expected type, make replacements, see if it all works out.

def _root_.String.Pos.Raw.rangeAt (pos : String.Pos.Raw) : Syntax.Range := ⟨pos, pos⟩

-- instance : Repr Language.Lean.CommandParsedSnapshot where
--   reprPrec snap _ := s!"{snap.desc}: [{snap.stx}] {snap.elabSnap.elabSnap.get}"
open Skimmer in
public def main : IO Unit := do
  initSearchPath (← findSysroot)
  let inputCtx := Parser.mkInputContext sourceFileDummy "<dummy>"
  let (setup, snap) ← Skimmer.runFrontend inputCtx { mainModuleName := `Dummy }
  let some { headerParserState, headerState, commands } := snap.toCommandSnaps
    | IO.eprintln "Could not find snaps."
  let some r := setup.result?.get | IO.eprintln "Could not find setup."
    -- turn imports into skimmer build filepaths (do it the basic way for now)
  -- spawn a `lake exe working` on them if they don't exist (lake will do this in the future)
  -- read into `replacements`.
  IO.println s!"{repr r.stx.raw.getRangeWithTrailing?}; {headerParserState.pos}"
  let mut replacements : NameMap Name := {}
  let mut edits : Array Edit := #[] -- import actual `Edit` functionality here
  for snap in commands do
    IO.println "----"
    -- TODO: none of these capture the error where the date and identifier are flipped. What does?
    -- if snap.isFatal then
    --   IO.eprintln s!"Fatal snap {snap.isFatal}"
    -- if snap.parserState.recovering then
    --   IO.eprintln s!"Parser recovering" -- not convinced this will ever be populated
    -- if snap.getState.messages.hasErrors then
    --   IO.eprintln s!"Errors:\n{← snap.getState.messages.toArray.mapM (·.toString)}"
    -- TODO: could be useful to run in new state, but this is really a subprocess-version problem.
    match ← snap.runCommandElabM' inputCtx <| refactorDeprecated.post replacements edits with
    | .error ex => IO.eprintln (← ex.toMessageData.toString)
    | .ok (replacements', edits') =>
      replacements := replacements'
      edits := edits'
    IO.println s!"edits: {repr edits}\n{snap.getSyntax.reprint.getD "couldn't reprint"}"
  -- finally write olean.skimmed. don't bother with error handling yet
  -- TODO standardize edits postprocessing as part of what "edits" are. this should be an extensible part of introducing accumulation
  if edits.any (·.shouldReview) then
    edits := edits.push ⟨headerParserState.pos.rangeAt, "\nimport Skimmer.Review\n", false⟩
  edits := edits.qsortOrd
  IO.println s!"====\nedits: {repr edits}"
  IO.println s!"====\n{sourceFileDummy.applyEdits edits}"
  -- replaceDeprecated (r : NameMap Name) (e : Array String) :=
  --   return (r, e.push s!"another! (foo exists: {(← getEnv).find? `foo |>.isSome})")
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
