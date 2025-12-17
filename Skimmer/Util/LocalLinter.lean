module

public import Lean.Data.NameMap
public import Lean.Elab.Command
import Lean

/-! # `local_linter`

This file adds a command of convenience for locally adding a linter (and allowing updates to it).
-/

open Lean Elab Term Command Linter

syntax localLinterDef := ident " := " term
syntax localLinterClear := &"clear " (&"all" <|> ident)
syntax localLinterArgs := localLinterClear <|> localLinterDef

syntax "local_linter " localLinterArgs : command

elab_rules : command
| `(command| local_linter $name:ident := $code:term) => unsafe liftTermElabM do
  let val ← withoutErrToSorry <| withSynthesize <|
    elabTermEnsuringType code (Expr.const ``CommandElab [])
  -- TODO: investigate why `local_linter foo := fun` reaches unreachable code;
  -- this is a hack that prevents that.
  let axioms ← val.getUsedConstants.mapM collectAxioms
  if axioms.any (·.contains ``sorryAx) then return

  let name := mkPrivateName (← getEnv) <| name.getId ++ `localLinter
   -- TODO: correct `checkMeta`?
  let run ← Meta.evalExpr CommandElab (Expr.const ``CommandElab [])
    (← instantiateMVars val) (checkMeta := true)
  lintersRef.modify fun a => a.eraseP (·.name == name) |>.push { name, run }
| `(command| local_linter clear all) =>
  lintersRef.modify fun a => a.eraseP ((`localLinter).isSuffixOf ·.name)
| `(command| local_linter clear $name:ident) =>
  lintersRef.modify fun a => a.eraseP ((name.getId ++ `localLinter).isSuffixOf ·.name)
