import Skimmer.LinterWithCleanup.Run

/-!
We provide a way to construct a `LinterWithCleanup` that handles an `IO.Ref`.

```lean
initialize myRef : IO.Ref κ ← IO.mkRef init

def myPLinter : PersistentLinter ρ κ where
  ref           := myRef
  add r k       := _ : κ
  persist k env := _ : Environment
  produce? stx  := _ : CommandElabM (Option ρ)
  runOnEOI, runOnHeader, shouldCleanup := _ : CommandElabM Bool

initialize addPersistentLinter myPLinter
```
-/

open Lean Elab Command

-- TODO: consider rename `PersistentLinter` ↦ `StatefulLinterWithCleanup`, `AccumulativeLinter` ↦ `PersistentLinter`

-- Could potentially fold into `PersistentLinter`.
structure PersistentRef (ρ κ) where
  ref     : IO.Ref κ
  add     : ρ → κ → κ
  persist : κ → Environment → Environment
deriving Nonempty

structure PersistentLinter (ρ κ) extends PersistentRef ρ κ, LinterWithCleanupSettings where
  produce? : Syntax → CommandElabM (Option ρ)
deriving Nonempty

def PersistentLinter.toLinterWithCleanup (l : PersistentLinter ρ κ) : LinterWithCleanup :=
  { l with
    run stx := do
      let some v ← l.produce? stx | return
      l.ref.modify (l.add v)
    cleanup := do
      let k ← l.ref.get
      modifyEnv (l.persist k)
  }

def addPersistentLinter (l : PersistentLinter ρ κ) : IO Unit := addLinterWithCleanup l.toLinterWithCleanup

-- Include `*Descr` versions? Not really necessary, just saving an `initialize myRef`.

/-!
### AccumulativeLinter

`AccumulativeLinter`s are `PersistentLinter`s which `persist` their data by feeding into a `PersistentEnvExtension`.
-/

structure AccumulativeLinterDescrBase (β ρ κ) extends LinterWithCleanupSettings where
  -- Part of what can be thought of as `PersistentRefDescr`, but we fix a factor of `persist` and leave free only the factor that yields the updates
  init : κ
  add : ρ → κ → κ
  submit : κ → Array β
  -- Linter
  produce? : Syntax → CommandElabM (Option ρ)

structure AccumulativeLinterDescr (α β σ ρ κ)
extends AccumulativeLinterDescrBase β ρ κ, PersistentEnvExtensionDescr α β σ

structure AccumulativeLinter (α β σ ρ κ) extends PersistentLinter ρ κ where
  ext : PersistentEnvExtension α β σ

instance [Inhabited σ] [Nonempty κ] [Nonempty ρ] :
    Nonempty (AccumulativeLinter α β σ ρ κ) :=
  ⟨{ toPersistentLinter := Classical.ofNonempty, ext := Classical.ofNonempty }⟩

def registerAndAddAccumulativeLinterUsingExt
    (ext : PersistentEnvExtension α β σ)
    (a : AccumulativeLinterDescrBase β ρ κ) : IO (AccumulativeLinter α β σ ρ κ) := do
  let ref ← IO.mkRef a.init
  let persistentLinter : PersistentLinter ρ κ := { a with
    ref
    persist k env := Id.run do
      let bs := a.submit k
      if bs.isEmpty then return env else
        let mut env := env
        for b in bs do
          env := ext.addEntry env b -- do we need to allow the descr to set async args?
        return env
  }
  addPersistentLinter persistentLinter
  return { persistentLinter with ext }

def registerAndAddAccumulativeLinter [Inhabited σ]
    (a : AccumulativeLinterDescr α β σ ρ κ) : IO (AccumulativeLinter α β σ ρ κ) := do
  let ext ← registerPersistentEnvExtension a.toPersistentEnvExtensionDescr
  registerAndAddAccumulativeLinterUsingExt ext a.toAccumulativeLinterDescrBase

/-!
### SimpleAccumulativeLinter

`SimpleAccumulativeLinter`s store values of type `β` used to update the environment extension in an `IO.Ref (Array β)`, and add the contents of the array in sequence to the extension.
-/

def SimpleAccumulativeLinter (α β σ) := AccumulativeLinter α β σ β (Array β)

instance [Inhabited σ] [Nonempty β] : Nonempty (SimpleAccumulativeLinter α β σ) :=
  ⟨{ toPersistentLinter := Classical.ofNonempty, ext := Classical.ofNonempty }⟩

structure SimpleAccumulativeLinterDescrBase β extends LinterWithCleanupSettings where
  produce? : Syntax → CommandElabM (Option β)

structure SimpleAccumulativeLinterDescr (α β σ)
extends SimpleAccumulativeLinterDescrBase β, PersistentEnvExtensionDescr α β σ

def SimpleAccumulativeLinterDescrBase.toAccumulativeLinterDescrBase
    (s : SimpleAccumulativeLinterDescrBase β) :
    AccumulativeLinterDescrBase β β (Array β) :=
  { s with
    init := #[]
    add b bs := bs.push b
    submit := id
  }

def SimpleAccumulativeLinterDescr.toAccumulativeLinterDescr
    (s : SimpleAccumulativeLinterDescr α β σ) :
    AccumulativeLinterDescr α β σ β (Array β) where
  toAccumulativeLinterDescrBase := s.toAccumulativeLinterDescrBase
  toPersistentEnvExtensionDescr := s.toPersistentEnvExtensionDescr

def registerAndAddSimpleAccumulativeLinterUsingExt [Inhabited σ]
    (ext : PersistentEnvExtension α β σ)
    (s : SimpleAccumulativeLinterDescrBase β) :
    IO (SimpleAccumulativeLinter α β σ) :=
  registerAndAddAccumulativeLinterUsingExt ext s.toAccumulativeLinterDescrBase

def registerAndAddSimpleAccumulativeLinter [Inhabited σ]
    (s : SimpleAccumulativeLinterDescr α β σ) :
    IO (SimpleAccumulativeLinter α β σ) :=
  registerAndAddAccumulativeLinter s.toAccumulativeLinterDescr
