import EditTest.Accumulator.Reflike
import EditTest.Accumulator.SourceIndexed

/-
We want to decouple the state from StatefulLinter, which is not that useful, I think.

Instead, we want a ref + extension + cleanup setup, then a toLinter thing.

If we use a ref for cleanups instead of an attribute, we can use `addCleanup` like `addLinter`
----
Hmm, we clearly want to be able to reuse an extension for another accumulator.
Would be cool to keep records of all of the cleanups which feed into the accumulator; need log options for the accumulator.

Makes you wonder if we can directly piggyback? or if we want to be able to define the extension independently easily. let you take apart the parts how you want.

Also need appropriate set_options.
---
After some thought:

- The base is the extension.
- Just above it is the cleanup function. This ought to be an implementation detail/boilerplate, at least.
- The Refs live above the extension and are connected to it by the cleanup. We can consolidate and have multiple linters use a single ref, or have a ref for each linter.
We
- The linters live above that. We can have multiple linters use the same ref—but *only* if we can add a name indexing somehow. E.g. `SourceAndLinterIndexed`.
-/

/-
initialize foo : Accumulator ← registerAccumulator accDescr

@[cleanup] def foo.cleanup : CommandElab := foo.toCleanup

initialize addLinter foo.toLinter
-/

open Lean Elab Command


/-- Accumulators are relations from mutable refs to environment extensions. They can be used to persist data in the environment from within contexts that cannot modify the environment, such as linters.

The relation between refs and extensions given by the collection of registered accumulators may be many-to-one and one-to-many: different accumulators may source data from the same ref, and different accumulators may incorporate data into the same extension. -/
structure Accumulator (ρ) (α β σ) (Ref) [Reflike Ref] where
  name : Name := by exact decl_name%
  ref : Ref ρ
  ext : PersistentEnvExtension α β σ
  /-- Incorporate the final state of the ref into the state of the environment extension; like `addEntryFn`, but is only expected to be run once, by the associated cleanup.

  TODO: rename, signaling the fact that this will run once at the end. `sendOff`? `submit`? -/
  incorporate : σ → ρ → σ


abbrev SimpleAccumulatorExtension (α) := PersistentEnvExtension α (Array α) (Array α)

def registerSimpleAccumulatorExtension {α} (name : Name := by exact decl_name%) :
    IO (SimpleAccumulatorExtension α) :=
  registerPersistentEnvExtension {
    name
    mkInitial := pure #[]
    addImportedFn _ := pure #[]
    addEntryFn := .append -- Allows modifying the state directly, earlier
    exportEntriesFnEx _ a _ := a
    statsFn a := f!"Accumulator extension {name}:\n\
      recorded {a.size} {if a.size = 1 then "entry" else "entries"}"
    asyncMode := .sync -- hmm...
    replay? := none -- Not exactly sure when we'd want this.
  }

def AccumulatorRef

-- instance [Reflike Ref] [IndexesSource SourceIndexed] [Inhabited <| Ref (SourceIndexed β)] : Inhabited <| Accumulator (β) (α) (αExported) (SourceIndexed)
--     (Ref : Type → Type) := ⟨{
--       recordInLinter? := default
--       append := default
--       ref := default
--       ext := default
--       exportEntriesFnEx := default
--     }⟩

-- instance [Reflike Ref] [IndexesSource SourceIndexed]
--     [i : Nonempty <| Ref (SourceIndexed β)] : Nonempty <| Accumulator (β) (α) (αExported) (SourceIndexed)
--     (Ref : Type → Type) := ⟨{
--       recordInLinter? := default
--       append := default
--       ref := Classical.choice i
--       ext := default
--       exportEntriesFnEx := default
--     }⟩

namespace AccumulatorDescr

-- elab "#in_server" : command => do
--   logInfo m!"{← getBoolOption Elab.inServer.name Elab.inServer.defValue}"

-- def getTrackingScope {αExported β α} {SourceIndexed Ref} [IndexesSource SourceIndexed] [Reflike Ref] {m : Type → Type} [Monad m] [MonadOptions m]
--     (a : AccumulatorDescr β α SourceIndexed Ref αExported) : m (Option InteractiveTrackingScope) := do
--   if ← getBoolOption Elab.inServer.name Elab.inServer.defValue then
--     return some a.interactiveTrackingScope
--   else
--     return none

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
