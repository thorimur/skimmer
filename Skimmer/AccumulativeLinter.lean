/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.LinterWithCleanup.Run
import Skimmer.LinterWithCleanup.Defs -- TODO: why is this necessary?

@[expose] public section

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

structure PersistentLinterBase ρ κ ε extends LinterWithCleanupSettings where
  name : Name := by exact decl_name%
  -- Ref
  add       : ρ → κ → κ
  shouldAdd : ρ → Bool := fun _ => true
  persist   : ε → Environment → Environment
  -- Linter
  produce : Syntax → CommandElabM ρ
  produceOnHeader? : Option (Substring.Raw → Syntax → CommandElabM ρ) := none
  submit : κ → CommandElabM ε

-- why can't deriving do this?
instance [Nonempty κ] : Nonempty (PersistentLinterBase ρ κ ε) := ⟨by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals exact Classical.ofNonempty
⟩

structure PersistentLinter (ρ κ ε) extends PersistentLinterBase ρ κ ε where
  ref : IO.Ref κ
deriving Nonempty

def PersistentLinter.toLinterWithCleanup (l : PersistentLinter ρ κ ε) : LinterWithCleanup :=
  { l with
    run stx := do
      let r ← l.produce stx
      if l.shouldAdd r then
        l.ref.modify (l.add r)
    runOnHeader := l.produceOnHeader?.map fun produceOnHeader =>
      fun ws stx => do
        let r ← produceOnHeader ws stx
        if l.shouldAdd r then
          l.ref.modify (l.add r)
    cleanup := do
      let k ← l.ref.get
      let e ← l.submit k
      modifyEnv (l.persist e) -- or use `setEnv`?
  }

@[inline] def addPersistentLinter (l : PersistentLinter ρ κ ε) : IO Unit :=
  addLinterWithCleanup l.toLinterWithCleanup

structure PersistentLinterDescr (ρ κ ε) extends PersistentLinterBase ρ κ ε where
  init : κ

-- Note: could expose the ref with e.g. `registerAndAddPersistentLinterDescr` or something.
-- But may as well just initialize it separately and include it in an `addPersistentLinterCall`.

@[inline] def addPersistentLinterDescr [Inhabited κ]
    (l : PersistentLinterDescr α β σ) : IO Unit := do
  let ref ← IO.mkRef l.init
  addPersistentLinter { l with ref }

/-!
### AccumulativeLinter

`AccumulativeLinter`s are `PersistentLinter`s which `persist` their data by feeding into a `PersistentEnvExtension`.
-/

structure AccumulativeLinterDescr (α β σ ρ κ γ)
  extends PersistentLinterDescr ρ κ (Array γ), PersistentEnvExtensionDescr α β σ where

structure AccumulativeLinter (α β σ ρ κ γ) extends PersistentLinter ρ κ (Array γ) where
  ext : PersistentEnvExtension α β σ

instance [Inhabited σ] [Nonempty κ] [Nonempty ρ] :
    Nonempty (AccumulativeLinter α β σ ρ κ γ) :=
  ⟨{ toPersistentLinter := Classical.ofNonempty, ext := Classical.ofNonempty }⟩

protected def AccumulativeLinter.registerAndAddUsingExt
    (ext : PersistentEnvExtension α β σ)
    (a : PersistentLinterDescr ρ κ (Array γ)) : IO (AccumulativeLinter α β σ ρ κ γ) := do
  let ref ← IO.mkRef a.init
  let persistentLinter : PersistentLinter ρ κ (Array γ) := { a with ref }
  addPersistentLinter persistentLinter
  return { persistentLinter with ext }

protected def AccumulativeLinter.registerAndAdd [Inhabited σ]
    (a : AccumulativeLinterDescr α β σ ρ κ γ) : IO (AccumulativeLinter α β σ ρ κ γ) := do
  let ext ← registerPersistentEnvExtension a.toPersistentEnvExtensionDescr
  AccumulativeLinter.registerAndAddUsingExt ext a.toPersistentLinterDescr

/-!
### SimpleAppendLinter

`SimpleAppendLinter`s stores an `IO.Ref (Array γ)`, and adds the contents of the array to the extension. It uses `Array.append` as opposed to arrays of arrays.
-/

def SimpleAppendLinter γ := AccumulativeLinter γ (Array γ) (Array γ) (Array γ) (Array γ) γ

deriving instance Nonempty for SimpleAppendLinter

structure SimpleAppendLinterDescr (γ) where
  name    : Name := by exact decl_name%
  statsFn : Array γ → Format := fun a => f!"AppendLinter {name}: {a.size} entries"
  produce : Syntax → CommandElabM (Array γ)

protected def SimpleAppendLinterDescr.toPersistentEnvExtensionDescr (γ)
    (descr : SimpleAppendLinterDescr γ) :
    PersistentEnvExtensionDescr γ (Array γ) (Array γ) where
  name := descr.name.appendAfter "Ext"
  statsFn := descr.statsFn
  mkInitial := pure #[]
  addImportedFn := fun _ => pure #[]
  addEntryFn := Array.append
  exportEntriesFnEx _ a _ := a

protected def SimpleAppendLinter.registerAndAddUsingExt
    (ext : PersistentEnvExtension γ (Array γ) (Array γ))
    (s : SimpleAppendLinterDescr γ) :
    IO (SimpleAppendLinter γ) :=
  let l := { s with
    init := #[]
    shouldAdd a := !a.isEmpty
    add := Array.append
    persist a env := ext.addEntry env a
    submit := pure
  }
  AccumulativeLinter.registerAndAddUsingExt ext l

protected def SimpleAppendLinter.registerAndAdd [Inhabited γ]
    (s : SimpleAppendLinterDescr γ) :
    IO (SimpleAppendLinter γ) := do
  let ext ← registerPersistentEnvExtension s.toPersistentEnvExtensionDescr
  SimpleAppendLinter.registerAndAddUsingExt ext s
