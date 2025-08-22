import EditTest.StatefulLinter.Add

open Lean Elab Command

structure AccumulativeLinterDescr (β) (α) where
  /-- Records a value of type `β` for a given command (or not). -/
  -- allow access to ref?
  record : Syntax → CommandElabM (Option β)
  /-- At the end of the file, appends each recorded value to the exported state. -/
  append : Array α → VersionedLine × β → Array α
  /-- When used interactively, determines scope. -/
  interactiveTrackingScope : InteractiveTrackingScope := .upToCommandEnd
  statsFn : Array α → Format := fun arr =>
    f!"Recording {arr.size} {if arr.size = 1 then "entry" else "entries"}"
  name : Name := by exact decl_name%

structure AccumulativeLinter (β) (α) (SourceIndexed) [IndexesSource SourceIndexed]
    (Ref : Type → Type) extends AccumulativeLinterDescr β α where
  ref : Ref (SourceIndexed β)
  ext : PersistentEnvExtension α (Array α) (Array α)

namespace AccumulativeLinterDescr

def toPersistentEnvExtensionDescr {α β} (a : AccumulativeLinterDescr β α) :
    PersistentEnvExtensionDescr α (Array α) (Array α) where
  name := a.name ++ `ext
  mkInitial := pure #[]
  addImportedFn _ := pure #[]
  addEntryFn _ new := new -- ignore prior state, since this is only called once
  exportEntriesFnEx _ a _ := a -- allow oleanlevel-dependent behavior?
  statsFn := a.statsFn
  asyncMode := .sync
  replay? := none

-- elab "#in_server" : command => do
--   logInfo m!"{← getBoolOption Elab.inServer.name Elab.inServer.defValue}"

def getTrackingScope {β α} {m : Type → Type} [Monad m] [MonadOptions m]
    (a : AccumulativeLinterDescr β α) : m (Option InteractiveTrackingScope) := do
  if ← getBoolOption Elab.inServer.name Elab.inServer.defValue then
    return some a.interactiveTrackingScope
  else
    return none

def toStatefulLinter
    (Ref : Type → Type) [Reflike Ref] {α β}
    (SourceIndexed) [IndexesSource SourceIndexed]
    (a : AccumulativeLinterDescr β α) : StatefulLinter (SourceIndexed β) Ref where
  run r stx := do
    let some b ← a.record stx | return
    let some vline := stx.getVersionedLine? (← getFileMap) (← a.getTrackingScope)
      | throwError "Could not get range for {stx}"
    Reflike.modify r fun state => IndexesSource.insert state vline b
  name := a.name

end AccumulativeLinterDescr

def addAccumulativeLinter {α β} (a : AccumulativeLinterDescr β α)
    (Ref : Type → Type) [Reflike Ref]
    (SourceIndexed := SourceIndexedArray) [IndexesSource SourceIndexed] (addLinter := true) :
    IO (AccumulativeLinter β α SourceIndexed Ref) := do
  let ref ← addStatefulLinter (addLinter := addLinter) <| a.toStatefulLinter Ref SourceIndexed
  let ext ← registerPersistentEnvExtension a.toPersistentEnvExtensionDescr
  return { a with ref, ext }

def AccumulativeLinter.toCleanup {β α SourceIndexed Ref}
    [IndexesSource SourceIndexed] [Reflike Ref]
    (a : AccumulativeLinter β α SourceIndexed Ref) : CommandElab := fun _ => do
  -- should we use modifyEnv or setEnv?
  let recorded ← Reflike.get a.ref
  let exported := IndexesSource.foldl recorded (init := #[]) fun arr v b =>
    a.append arr (v, b)
  modifyEnv fun env => a.ext.addEntry env exported

open Parser in
/-- Initialize an accumulative linter, and register a cleanup function that persists the data. -/
syntax (name := initializeAccumulativeLinter)
  declModifiers "initialize_accumulative_linter "
  (atomic(ident (Term.typeSpec)? ppSpace Term.leftArrow)) Term.doSeq : command


macro_rules
| `(initializeAccumulativeLinter|
  $declModifiers:declModifiers initialize_accumulative_linter%$tk $id $[: $type?]? ← $doSeq) => do
  let init ← if let some type := type? then
      `(Parser.Command.«initialize»|
        $declModifiers:declModifiers initialize%$tk $id:ident : AccumulativeLinter _ _ _ ← do show $type from do $doSeq)
    else
      `(Parser.Command.«initialize»|
        $declModifiers:declModifiers initialize%$tk $id:ident : AccumulativeLinter _ _ _ ← $doSeq)
  let cleanup ← withRef tk `(command|
    @[cleanup] def $(mkIdentFrom id <| id.getId ++ `cleanup) : Lean.Elab.Command.CommandElab :=
      AccumulativeLinter.toCleanup $id)
  pure <| mkNullNode #[init, cleanup]

/-

initialize myRef ← addStatefulLinter myStatefulLinter
initialize myExt ← registerPersistentEnvExtension myPersistentEnvExtensionDescr

@[cleanup]
def myLinter.cleanup : CommandElab := toCleanup myRef myExt

-/
