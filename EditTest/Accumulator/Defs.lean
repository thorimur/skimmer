import EditTest.Accumulator.Reflike
import EditTest.Accumulator.SourceIndexed

/-
We want to decouple the state from StatefulLinter, which is not that useful, I think.

Instead, we want a ref + extension + cleanup setup, then a toLinter thing.

If we use a ref for cleanups instead of an attribute, we can use `addCleanup` like `addLinter`
-/

/-
initialize foo : Accumulator ← registerAccumulator accDescr

@[cleanup] def foo.cleanup : CommandElab := foo.toCleanup

initialize addLinter foo.toLinter
-/

open Lean Elab Command

structure AccumulatorDescr (β) (α) (SourceIndexed) (Ref)
    [IndexesSource SourceIndexed] [Reflike Ref] (αExported := α) where
  name : Name := by exact decl_name%
  -- TODO: Should probably move out of here; only used in linter.
  /-- Produces a value of type `β` for a given command (or not). -/
  recordInLinter? : Syntax → CommandElabM (Option β)
  /-- At the end of the file, appends each recorded value to the exported state. -/
  append : Array α → VersionedLine × β → Array α
  /-- When used interactively, determines scope. -/
  interactiveTrackingScope : InteractiveTrackingScope := .upToCommandEnd
  statsFn : Array α → Format := fun arr =>
    f!"Recorded {arr.size} {if arr.size = 1 then "entry" else "entries"}"
  exportEntriesFnEx : Environment → Array α → OLeanLevel → Array αExported :=
    by exact fun _ a _ => a
  -- Should we have `cleanup : Ref (SourceIndexed β) → PersistentEnvExtension _ _ _ → COmmandElab` with a default? or `customCleanup? : Option ..`? or just let it be defined at the boilerplate level

structure Accumulator (β) (α) (αExported) (SourceIndexed)
    (Ref : Type → Type) [IndexesSource SourceIndexed] [Reflike Ref] extends AccumulatorDescr β α SourceIndexed Ref αExported where
  ref : Ref (SourceIndexed β)
  ext : PersistentEnvExtension αExported (Array α) (Array α)

namespace AccumulatorDescr

def toPersistentEnvExtensionDescr {αExported α β} [IndexesSource SourceIndexed] [Reflike Ref] (a : AccumulatorDescr β α SourceIndexed Ref αExported) :
    PersistentEnvExtensionDescr αExported (Array α) (Array α) where
  name := a.name ++ `ext
  mkInitial := pure #[]
  addImportedFn _ := pure #[]
  -- allows us to add to a state which may be modified by other elaborators
  addEntryFn := Array.append
  exportEntriesFnEx := a.exportEntriesFnEx
  statsFn := a.statsFn
  asyncMode := .sync
  replay? := none

-- elab "#in_server" : command => do
--   logInfo m!"{← getBoolOption Elab.inServer.name Elab.inServer.defValue}"

def getTrackingScope {αExported β α} {SourceIndexed Ref} [IndexesSource SourceIndexed] [Reflike Ref] {m : Type → Type} [Monad m] [MonadOptions m]
    (a : AccumulatorDescr β α SourceIndexed Ref αExported) : m (Option InteractiveTrackingScope) := do
  if ← getBoolOption Elab.inServer.name Elab.inServer.defValue then
    return some a.interactiveTrackingScope
  else
    return none

def registerAccumulator {αExported β α}
    {SourceIndexed Ref} [IndexesSource SourceIndexed] [Reflike Ref]
    (a : AccumulatorDescr β α SourceIndexed Ref αExported) :
    IO (Accumulator β α αExported SourceIndexed Ref) := do
  let ref : Ref (SourceIndexed β) ← Reflike.new {}
  let ext ← registerPersistentEnvExtension a.toPersistentEnvExtensionDescr
  return { a with ref, ext }

end AccumulatorDescr

namespace Accumulator

@[inline] def toCleanup {αExported β α SourceIndexed Ref}
    [IndexesSource SourceIndexed] [Reflike Ref]
    (a : Accumulator β α αExported SourceIndexed Ref) : CommandElab := fun _ => do
  -- should we use modifyEnv or setEnv?
  let recorded ← Reflike.get a.ref
  let exported := IndexesSource.foldl recorded (init := #[]) fun arr v b =>
    a.append arr (v, b)
  modifyEnv fun env => a.ext.addEntry env exported

def record {β α αExported}
    {Ref : Type → Type} [Reflike Ref]
    {SourceIndexed} [IndexesSource SourceIndexed]
    (a : Accumulator β α αExported SourceIndexed Ref) (line : VersionedLine) (value : β)
    {m} [Monad m] [MonadLiftT BaseIO m] [MonadOptions m] [MonadFileMap m] : m Unit := do
  Reflike.modify a.ref fun state => IndexesSource.insert state line value

def recordAt {β α αExported}
    {Ref : Type → Type} [Reflike Ref]
    {SourceIndexed} [IndexesSource SourceIndexed]
    (a : Accumulator β α αExported SourceIndexed Ref) (ref : Syntax) (value : β)
    {m} [Monad m]
    [MonadLiftT BaseIO m] [MonadOptions m] [MonadFileMap m] [MonadError m] : m Unit := do
  let some vline := ref.getVersionedLine? (← getFileMap) (← a.getTrackingScope)
    | throwError "Error recording value in {a.name}:\nCould not get range for {ref}"
  a.record vline value

@[inline] def toLinter {β α αExported}
    {Ref : Type → Type} [Reflike Ref]
    {SourceIndexed} [IndexesSource SourceIndexed]
    (a : Accumulator β α αExported SourceIndexed Ref) : Linter where
  run stx := do
    let some value ← a.recordInLinter? stx | return
    a.recordAt stx value
  name := a.name

end Accumulator

open Parser in
-- TODO: toggles for cleanup etc.
syntax (name := initializeAccumulator)
  declModifiers "initialize_accumulator "
  (atomic(ident (Term.typeSpec)? ppSpace Term.leftArrow)) Term.doSeq : command


macro_rules -- TODO (WIP)
| `(initializeAccumulator|
  $declModifiers:declModifiers initialize_accumulator%$tk $id $[: $type?]? ← $doSeq) => do
  let init ← if let some type := type? then
      `(Parser.Command.«initialize»|
        $declModifiers:declModifiers initialize%$tk $id:ident : Accumulator _ _ _ _ _ ← do show $type from do $doSeq)
    else
      `(Parser.Command.«initialize»|
        $declModifiers:declModifiers initialize%$tk $id:ident : Accumulator _ _ _ _ _ ← $doSeq)
  let addLinter ← withRef tk `(Parser.Command.«initialize»|
        $declModifiers:declModifiers initialize%$tk ← addLinter (Accumulator.toLinter $id))
  let cleanup ← withRef tk `(command|
    @[cleanup] def $(mkIdentFrom id <| id.getId ++ `cleanup) : Lean.Elab.Command.CommandElab :=
      AccumulativeLinter.toCleanup $id)
  pure <| mkNullNode #[init, addLinter, cleanup]

/-

initialize myRef ← addStatefulLinter myStatefulLinter
initialize myExt ← registerPersistentEnvExtension myPersistentEnvExtensionDescr

@[cleanup]
def myLinter.cleanup : CommandElab := toCleanup myRef myExt

-/
