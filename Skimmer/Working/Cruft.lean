module

import Lean
import all Lean.Language.Lean
public import Lean.Elab.Frontend

open Lean Elab Command

-- #check System.FilePath

-- #check Language.Lean.HeaderParsedSnapshot
-- #check Language.Snapshot
-- #check Language.Lean.HeaderParsedSnapshot -- resulting parser state, syntax of header, initial input context (before parsing) for reuse
-- #check Language.Lean.HeaderProcessedSnapshot -- post-setup/importing, contains initial `Command.State` *and* snapshot of next command
-- #check Language.Lean.SetupImportsResult
-- #check Server.FileWorker.setupImports -- not what we want, but an example

#check runFrontend -- this sets things up


-- #check Parser.mkInputContext

-- #check Language.ProcessingT -- apparently just allows access to an inputCtx via a reader...?

public section

namespace Skimmer

open Lean Language Lean Elab

-- #check Lean.HeaderProcessedSnapshot -- file headers
-- #check Elab.HeaderProcessedSnapshot -- definition headers
section
variable (stx : HeaderSyntax) (mainModuleName : Name) (opts : Options) (trustLevel : UInt32 := 0)
    (plugins : Array System.FilePath := #[])

/-- Ripped out of `runFrontend` for convenience. Assumes we don't have a `setup` to merge into as `runFrontend` optionally allows. As such, does not need to be monadic. We might want a monadic version if these values are in a convenient monad. -/
@[inline]
def runFrontend.setup : SetupImportsResult where
  imports := stx.imports
  isModule := stx.isModule
  mainModuleName
  opts
  trustLevel
  plugins

-- #check Parser.parseHeader
-- #check HeaderSyntax
def runFrontend.setupForProcessing (stx : HeaderSyntax) :
    ProcessingT IO (Except Lean.HeaderProcessedSnapshot SetupImportsResult) :=
  return .ok <| setup stx mainModuleName opts trustLevel plugins
end
/-
  let opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  -- default to async elaboration; see also `Elab.async` docs
  let opts := Elab.async.setIfNotSet opts true
-/
/-



-/


-- The way snapshots work for commands and such: each one is meant to contain the snapshot of the next command (if there is one). then you can wait on it and such.
-- We could do this, or we could go digging.

-- TODO: no
instance : Repr Options where
  reprPrec _ _ := f!"<options>"

deriving instance Repr, Inhabited for SetupImportsResult

#check ImportArtifacts
-- #check Lean.Language.Lean.process.parseHeader
-- #check Lean.Language.Lean.process.processHeader -- sets up env
-- #check Elab.processHeader
-- #check Elab.process

-- #check IO.processCommands
-- #check IO.processCommandsIncrementally -- why do these take Command.State?!

#check SnapshotTask

/-- Like `SetupImportsResult`, but also includes the header syntax. -/
structure ImportsSetup extends SetupImportsResult where
  stx : HeaderSyntax
deriving Repr, Inhabited

/-- Facts about the module that are inferred external to the module itself -/
structure ModuleSetupExternal where
  /-- The name of the module. -/
  mainModuleName : Name
  trustLevel : UInt32 := 0
  /-- The package to which the module belongs (if any). -/
  package? : Option PkgId := none
  /-- Dynamic libraries to load with the module. -/
  dynlibs : Array System.FilePath := #[]
  /-- Plugins to initialize with the module. -/
  plugins : Array System.FilePath := #[]
  /-- Additional options for the module. -/
  options : LeanOptions := {}
  -- TODO: not clear to me if imports and import artifacts should be here? does lake also provide these prior to the processing of the file somehow?

-- /-- Deliberate changes we may want to make to the module setup. We go field by field to allow them to be more easily altered independently... actually, no, they may need to interfere, right? -/
-- structure SetupChanges where
--   mainModuleNameChanges : Name → Name := id
--   packageChanges : Option PkgId → Option PkgId := id
--   trustLevelChanges : UInt32 → UInt32 := id
--   importChanges : Array Import → Array Import := id
--   importArtsChanges : NameMap ImportArtifacts → NameMap ImportArtifacts := id
--   dynlibChanges : Array System.FilePath → Array System.FilePath := id
--   pluginChanges : Array System.FilePath → Array System.FilePath := id
--   optsChanges : Options → Options := id
--   isModuleChanges : Bool → Bool := id

#print SetupImportsResult

/-- The same as `runFrontEnd`, but
1. stores the `SetupImportsResult` in a promise to grab it later (sigh, wish it was in a snap)
    TODO: is there a better way?
2. stops after producing the snapshot tree
3. does not time
4. asks for an input context instead of an input and filename
5. allows changing the `SetupImportsResult`, but not through the given ModuleSetup as before
6. allows the caller to supply `old?` for reuse -/
protected def runFrontend
    -- (input : String)
    -- (fileName : String)
    (inputCtx : Parser.InputContext)
    (moduleSetup : ModuleSetupExternal) -- subsumes mainModuleName + some of setup?
    -- (oleanFileName? : Option System.FilePath := none)
    -- (ileanFileName? : Option System.FilePath := none)
    -- (jsonOutput : Bool := false)
    -- (errorOnKinds : Array Name := #[])
    -- (printStats : Bool := false)
    -- TODO: not sure if a big old function here is necessary or performant, but it is versatile
    (setupChanges? : Option (SetupImportsResult → ProcessingT IO SetupImportsResult) := none)
    (old? : Option InitialSnapshot := none)
    : IO (IO.Promise ImportsSetup × InitialSnapshot) := do
  -- let startTime := (← IO.monoNanosNow).toFloat / 1000000000
  -- let inputCtx := Parser.mkInputContext input fileName
  let opts := Lean.internal.cmdlineSnapshots.set moduleSetup.options.toOptions true
  -- default to async elaboration; see also `Elab.async` docs
  let opts := Elab.async.setIfNotSet opts true
  let ctx := { inputCtx with }
  let setupProm : IO.Promise ImportsSetup ← IO.Promise.new
  let setup stx := do
    -- change begin
    let mut setup : SetupImportsResult := {
          trustLevel := moduleSetup.trustLevel
          package? := moduleSetup.package?
          mainModuleName := moduleSetup.mainModuleName
          isModule := stx.isModule
          imports := stx.imports
          -- importArts? should we include in external?
          plugins := moduleSetup.plugins
          opts
        }
    if let some setupChanges := setupChanges? then
      setup ← setupChanges setup
    setupProm.resolve { setup with stx }
    return .ok setup
    -- change end
  let processor := Language.Lean.process
  let snaps ← processor setup old? ctx
  return (setupProm, snaps)

-- TODO: currently `setup` is bound up in `Language.Lean.process`. Might be nice to split it out and only continue to fill the snaps when we want to.

#check String.Slice.dropPrefix?

end Skimmer

/-- Gets the syntax of the top-level node, assuming there is one. -/
partial def Lean.Elab.InfoTree.getSyntax? (t : InfoTree) : Option Syntax :=
  match t with
  | .node i _    => i.stx
  | .context _ t => t.getSyntax?
  | .hole _      => none

#check PartialContextInfo

/-- Gets the syntax of the top-level node, or returns `.missing` if there isn't one. -/
partial def Lean.Elab.InfoTree.getSyntax (t : InfoTree) : Syntax :=
  match t with
  | .node i _    => i.stx
  | .context _ t => t.getSyntax
  | .hole _      => .missing

#check CommandContextInfo
-- Not actually the env before
-- /-- Gets the syntax of the top-level node, or returns `.missing` if there isn't one. -/
-- partial def Lean.Elab.InfoTree.getEnvBefore? (t : InfoTree) : Option Environment :=
--   match t with
--   | .node _ ts    => ts.findSome? (·.getEnvBefore?) --bad?
--   | .context (.commandCtx info) _ => info.env
--   | .context _ t => t.getEnvBefore? -- shouldn't happen?
--   | .hole _      => none

partial def Lean.Elab.InfoTree.getEnv? (t : InfoTree) : Option Environment :=
  match t with
  | .node _ ts    => ts.findSome? (·.getEnv?) --bad?
  | .context (.commandCtx info) _ => info.env
  | .context _ t => t.getEnv? -- shouldn't happen?
  | .hole _      => none

/-- Gets the syntax of the top-level node, or returns `.missing` if there isn't one. -/
partial def Lean.Elab.InfoTree.getEnvAfter? (t : InfoTree) : Option Environment :=
  match t with
  | .node _ ts    => ts.findSome? (·.getEnvAfter?) --bad?
  | .context (.commandCtx info) _ => info.cmdEnv?
  | .context _ t => t.getEnvAfter? -- shouldn't happen?
  | .hole _      => none

namespace Lean.Language.Lean

/-- Convenience function; does it the way `IO.processCommandsIncrementally` does. Blocks. -/
-- TODO: why not `elabSnap.infoTree?`?
def CommandParsedSnapshot.getInfoTree? (snap : CommandParsedSnapshot) : Option InfoTree :=
  snap.elabSnap.infoTreeSnap.get.infoTree?

def CommandParsedSnapshot.getInfoTree! (snap : CommandParsedSnapshot) : InfoTree :=
  snap.getInfoTree?.get!

-- /-- TODO: eh...just lifts the option to IO -/
-- def CommandParsedSnapshot.getInfoTree (snap : CommandParsedSnapshot) : IO InfoTree :=
--   snap.getInfoTree?.getDM <| throw (.userError "Could not find infotree.")

/-- Blocks. Generally the other `stx` fields seem to be `missing`. TODO: investigate. am I missing an option or something? -/
-- TODO: why not `elabSnap.infoTree?`?
def CommandParsedSnapshot.getSyntax? (snap : CommandParsedSnapshot) : Option Syntax := do
  (← snap.getInfoTree?).getSyntax?

/-- Blocks. Gets the syntax Generally the other `stx` fields seem to be `missing`. -/
-- TODO: why not `elabSnap.infoTree?`?
def CommandParsedSnapshot.getSyntax (snap : CommandParsedSnapshot) : Syntax :=
  snap.getInfoTree?.elim .missing (·.getSyntax)

/--
Gets the command state *after* the command has been elaborated. However--no infotrees??

What is the relationship to (1) the infotree from `getInfoTree` (2) the diagnostic messages (3) the linter effect on messages? -/
def CommandParsedSnapshot.getState (snap : CommandParsedSnapshot) : Command.State :=
  { snap.elabSnap.resultSnap.get.cmdState with infoState := {
      trees := match snap.getInfoTree? with
        | some t => PersistentArray.empty.push t
        | none => {} }
      -- TODO: holes? do we need to substitutelazy or anything? what about the other infostate things? really confused by this cmdState.
  }

/-- Convenience function; does it the way `IO.processCommandsIncrementally` does. Blocks. -/
-- TODO: why not `elabSnap.infoTree?`?
def CommandParsedSnapshot.getPos (snap : CommandParsedSnapshot) : String.Pos.Raw :=
  snap.parserState.pos

structure CommandSnaps where
  headerParserState : Parser.ModuleParserState
  headerState : Command.State
  commands : Array CommandParsedSnapshot


/-- Gets all of the snapshots for the commands after the initial snapshot (which has information from just after the header has been parsed).

TODO: this is not a permanent design. Ideally we want to dispatch work as soon as the snap becomes available, so we want some sort of binding or mapping on the `SnapshotTask` instead of these blocking `get`s.

If we even continue to use snapshots at all, that is. But the incremental reuse is probably good for the computer while editing just as it is for the human.
-/
partial def InitialSnapshot.toCommandSnaps (snap : InitialSnapshot) :
    Option CommandSnaps := do
  -- Unfortunately this seems throw away nearly everything?
  let snap ← snap.result?
  let processedState ← snap.processedSnap.get.result? -- blocks
  return {
    headerParserState := snap.parserState
    headerState := processedState.cmdState
    commands := go processedState.firstCmdSnap.get #[]
  }
where
  go (snap : CommandParsedSnapshot) (cmds : Array CommandParsedSnapshot) :=
    if let some next := snap.nextCmdSnap? then
      go next.get (cmds.push snap)
    else
      cmds.push snap


-- Question: if new imports run new initializers, is it the case that we tear down the whole process when imports change? I feel like I read this somewhere.
#check IO.processCommandsIncrementally
/-
partial def IO.processCommandsIncrementally (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (commandState : Command.State)
    (old? : Option IncrementalState) :
    BaseIO IncrementalState := do
  let task ← Language.Lean.processCommands inputCtx parserState commandState
    (old?.map fun old => (old.inputCtx, old.initialSnap))
  go task.get task #[]
where
  go initialSnap t commands :=
    let snap := t.get
    let commands := commands.push snap
    if let some next := snap.nextCmdSnap? then
      go initialSnap next.task commands
    else
      -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
      -- all snapshots
      let messages := toSnapshotTree initialSnap
        |>.getAll.map (·.diagnostics.msgLog)
        |>.foldl (· ++ ·) {}
      -- In contrast to messages, we should collect info trees only from the top-level command
      -- snapshots as they subsume any info trees reported incrementally by their children.
      let trees := commands.map (·.elabSnap.infoTreeSnap.get.infoTree?) |>.filterMap id |>.toPArray'
      return {
        commandState := { snap.elabSnap.resultSnap.get.cmdState with messages, infoState.trees := trees }
        parserState := snap.parserState
        cmdPos := snap.parserState.pos
        commands := commands.map (·.stx)
        inputCtx, initialSnap
      }
-/
#check waitForFinalCmdState?
/-
/-- Waits for and returns final command state, if importing was successful. -/
partial def waitForFinalCmdState? (snap : InitialSnapshot) : Option Command.State := do
  let snap ← snap.result?
  let snap ← snap.processedSnap.get.result?
  goCmd snap.firstCmdSnap.get
where goCmd snap :=
  if let some next := snap.nextCmdSnap? then
    goCmd next.get
  else
    snap.elabSnap.resultSnap.get.cmdState
-/

/-
It's going to have the following flow

----
We're in a library/package. We're fed the **target** we want to refactor. Let's say for convenience it's a **single module**.

**mod**
 ↓
filepath -- could start here for convenience
 ↓ read
string

----
Then we need to get the header, and the imports, and everything needed for the environment. Ideally we also allow operating on the header here to create intermediate data.

string
 ↓ parse
header syntax + parser state
 ↓ "elab"
`Import`s (module names + modifiers)

  [future] might want to go full snapshot when doing the real thing, especially for reusing changes to imports. not necessary here.
-/

structure HeaderParsed where
  inputCtx : Parser.InputContext
  parserState : Parser.ModuleParserState -- just a position and whether we're recovering
  stx : HeaderSyntax
  imports : Array Import
  isModule : Bool
  messages : MessageLog

-- confused by filename. Is it a `System.FilePath` or what? TODO: clarify/standardize here.
-- convenience function
def parseHeaderToSetup (input fileName : String) : IO HeaderParsed := do
  let inputCtx := Parser.mkInputContext input fileName

  let (stx, parserState, messages) ← Parser.parseHeader inputCtx
  let stx : HeaderSyntax := stx -- type synonym
  return {
    inputCtx
    parserState
    stx
    imports := stx.imports
    isModule := stx.isModule
    messages
  }


/-
----
We also need the previous data.

`Import`s
 ↓
filepaths
 ↓
skimmer build artifact filepaths
 ↓
deserialize β
↘↓↙ merge
initial β state


----
Now we need to construct the environment in the orchestrator.
In the future this will be a subprocess...somehow.
For now we're hardcoding the folded state + functionality. In the future these will be general.

`Import`s
 ↓ importModules
env   ↙ Command.State? ↙ Syntax? Parser state? -- Where exactly do we parse + get the next cmd?
→↓ IO.processCommand or Language.Lean.processCommand or some other internal?
 ↓ ???
Array of `InfoTrees`, `Syntax` ???  ↙β
 ↓ tool
β + edits + next command state
↑←
...
{terminal command encountered}
 ↓
store β + edits in skimmer build artifact...writeModule? can we deserialize without init?

  [future] Possible interactivity + pickup point/suspended process instead of re-running.

----
Now we need to read the edits to display to the user.

filepath
 ↓
skimmer build artifact
 ↓ deserialize
displayed edits + button for writing them

---
To write the edits:

  [future] new git worktree, incorporate into loop with reparsing + re-elab

filepath
 ↓
skimmer build artifact
 ↓
deserialized edits
 ↓ write to source
(altered source file)


-- Idea/aside: representing no-op effects with wrapper types for Lake. They don't maintain reference to the actual jobs, but they tell us something like that there *will* be a file here, or something?


----
At the beginning:

dive file with syntax specifying module
 ↓
module
 ↓
...

-/


/-
# Environment fluency

- In the future we want to be have a metaprogramming API for *internal data capture*, i.e. by allowing a source-level metaprogram to catch data itself (a la the to_additive refactor). It can put stuff in the environment, then we read it.
- We can pass along data externally. The difficulty maybe is allowing this state to be extensible. We don't have any other environment to add it to, so for extensibility we **will** probably need to **add our things to the source environment**. This can be done during `importModules` or manually. Manual might make sense for attribute-only stuff? Not sure. (Ensure no conflict with source-imported versions of the same)
  - An alternative for extensibility is recompiling the executable with our refactors and such inlined.
  - Another alternative is using plugins, but carefully! E.g. dynlibs and such. Requires building shared facets and such for our tools though. Not too much of an issue if they're all in a library it sets up for you.
  - For now let's hardcode a single function


-/
