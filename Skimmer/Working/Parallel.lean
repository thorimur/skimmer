module

import Lean

/-!

Here, we define the combinators into which we feed "interventions".
We want to see what they need.

Questions:
- Monad state/context or not? **Probably yes, but not yet.**
-


-/

open Lean Elab Command

-- Probably nicer as a state monad...
abbrev InterventionM (m : Type → Type) (α) := Environment → α → m (α × Environment)

#check Frontend.elabCommandAtFrontend

/-
```
structure State where
  commandState : Command.State
  parserState  : Parser.ModuleParserState
  cmdPos       : String.Pos.Raw
  commands     : Array Syntax := #[]
deriving Nonempty

structure Context where
  inputCtx : Parser.InputContext

abbrev FrontendM := ReaderT Context $ StateRefT State IO
```

```
@[inline] def runCommandElabM (x : Command.CommandElabM α) : FrontendM α := do
  let ctx ← read
  let s ← get
  let cmdCtx : Command.Context := {
    cmdPos       := s.cmdPos
    fileName     := ctx.inputCtx.fileName
    fileMap      := ctx.inputCtx.fileMap
    snap?        := none
    cancelTk?    := none
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run s.commandState) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => setCommandState sNew; return a

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM do
    Command.elabCommandTopLevel stx
```


`runFrontendM` ~> `waitForFinalCmdState?` builds in the recursion. We want to pause here.
-/

/-
Lake stuff:

`Module.recBuildLean`
~> `Module.buildLean` (some nice file stuff)
~> `Lake.compileLeanModule` (`LogIO Unit`)
  - sorts out directories + files for oleans/ileans/etc. as cli arguments, then calls lean via `rawProc`

The lean executable called in this way eventually calls `runFrontend` via `shellMain`
-/

/-
There's a zoo of `process`-named functions to keep track of, with different signatures.

`Lean.Language.Lean`
- involves `LeanProcessingM`
- `processCommand (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State)
    (old? : Option (Parser.InputContext × CommandParsedSnapshot) := none) :
    BaseIO (Task CommandParsedSnapshot)`
- `waitForFinalCmdState?`

`Frontend`
- involves `FrontendM` which has command state, parser context, etc., and an array of commands

`IO`
- `IO.processCommandsIncrementally`, `IO.processCommands`, etc., seem totally unrelated to `FrontendM`, despite being in the same file. They rely on `Language.Lean.processCommands`, which in turn splits out a component of `Language.Lean.process`.
- Likewise `runFrontend` actually depends on `Language.Lean.process`, and does not involve `FrontendM` (returning an `IO (Option Environment)` and not taking in any `FrontendM` action)
- `runFrontend` does write all of the files, by the way—if they are provided.
-/

def importModules

/-
For flexibility, I think we want to have a monad in which to take actions or something? An API for jumping from process to process/forking and retaining communication? But how do we request things? Read-only memory? How do we work within two environments?

If you communicate information from one environment to another, it might not be interpretable in the new one. For example, passing out the whole environment.

What if we got used to working with `Inside envᵢ α`? Not necessarily good enough...also have things like `CommandElabM` state we care about. But the environment is the big one.

While source elaboration can kind of go off on its own, we want to *test and compute* within that process/its environment/its intermediate states, assuming we save them as needed.
-/

/-
  let a ← inSource do
    egergg
  let



-/

/-
Can we be async about the source file? Memory might explode but that could be okay...just need a way to read from it. Ideally whether we keep each stage or not is determined by some other thing...
-/


/-

-/

/-
Future thoughts
- Incremental reuse could be helpful for retrying things—just look at the snap
- We likely want custom task management, not simply `prom.result!` as in one of the `process`es
- We should accommodate all sorts of shapes/control flows for traversing both source and new source. Lean minimize is something it would be nice to subsume.
- We should split out the "dive file" interface library internals so other tools can create their own interface, kind of like `CliM` allows the creation of cli interfaces.
  - Re: two separate files, new modifications: can we include a lean file within a file by having another process which reports back? imports and all?
- People have security concerns, rightfully so. Can we run containerize automatically or something?
-/
