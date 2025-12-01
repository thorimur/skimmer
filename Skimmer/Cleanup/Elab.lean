/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Skimmer.Cleanup.Attr

@[expose] public section

open Lean Elab Command Parser

-- #check Language.DynamicSnapshot
-- #check Language.SnapshotTree.waitAll

-- def Lean.Elab.Command.waitForAllTasks : CommandElabM Unit := do
--   for snap in (← get).snapshotTasks do
--     let t ← (Language.toSnapshotTree snap.get).waitAll
--     let _ ← t.bind

--   let some snap := (← read).snap? | return
--   let some snap := snap.old? | return
--   Language.toSnapshotTree snap.val

-- use scoped, erased, etc.
meta def runCleanups : CommandElab := fun stx => do
  let cleanupss := cleanupAttr.ext.getImportedEntries (← getEnv)
  let localCleanups := cleanupAttr.ext.getState (← getEnv)
  -- `isEmpty` check worth it instead? or just let the loop run?
  for cleanups in cleanupss do
    for cleanup in cleanups do
      let act ← unsafe evalConstCheck CommandElab ``CommandElab cleanup
      act stx
  for cleanup in localCleanups do
    let act ← unsafe evalConstCheck CommandElab ``CommandElab cleanup
    act stx

  -- -- if we wanted to run all cleanups:
  -- let mut errors := #[]
  -- for cleanups in cleanupss do
  --   for cleanup in cleanups do
  --     let result := ((← getEnv).evalConstCheck CommandElab (← getOptions) ``CommandElab cleanup)
  --     match result with
  --     | .ok act => try act stx catch msg => errors := errors.push msg
  --     | .error msg => errors := errors.push (.error stx msg)
  -- for cleanup in localCleanups do
  --   let result := ((← getEnv).evalConstCheck CommandElab (← getOptions) ``CommandElab cleanup)
  --     match result with
  --     | .ok act => act stx
  --     | .error msg => errors := errors.push (.error stx msg)
  -- for error in errors do
  --   logErrorAt stx error.toMessageData


@[command_elab eoi]
meta def elabEoiToCleanups : CommandElab
| stx@(.node _ ``Command.eoi _) => do
  -- Wait for main environment branch; this does not account for linters.
  let _ := (← getEnv).checked.get
  runCleanups stx
| _ => throwUnsupportedSyntax
