module

public import Lean

open Lean Elab Term Linter

/-! # Utilities for showing metaprogramming information

-- TODO: environment, tactic states, terms, better infotree selection, widgets? etc.
-/

public meta section

/-- Show all inspected data. -/
register_option inspect : Bool := {
  defValue := false
  descr := "Show all inspected data."
}

/-- Show syntax for declarations. -/
register_option inspect.syntax : Bool := {
  defValue := false
  descr := "Show syntax."
}

/-- Show infotrees for declarations. -/
register_option inspect.info : Bool := {
  defValue := false
  descr := "Show infotrees."
}

/-- Use the `Repr` instance when showing syntax. -/
register_option inspect.syntax.repr : Bool := {
  defValue := false
  descr := "Display syntax using `Repr`."
}

/-- Show positions when formatting syntax. Only applies if `inspect.syntax.repr` is `false`. -/
register_option inspect.syntax.pos : Bool := {
  defValue := false
  descr := "Display syntax positions."
}

-- TODO: use `withSetOptionIn` when `#11313` lands.
-- TODO: single `logInfo`? prefix?
def inspectLinter : Linter where
  run stx := do
    if ← getBoolOption `inspect.syntax <||> getBoolOption `inspect then
      if ← getBoolOption `inspect.syntax.repr then
        logInfo m!"{repr stx}"
      else if ← getBoolOption `inspect.syntax.pos then
        logInfo m!"{stx.formatStx (showInfo := true)}"
      else
        logInfo m!"{format stx}"
    if ← getBoolOption `inspect.info <||> getBoolOption `inspect then
      for t in ← getInfoTrees do
        logInfo (← t.format)

initialize addLinter inspectLinter

/-! # `#view`

This simply makes looking at the syntax of terms a little easier.
-/



syntax (name := i) "#i " term : command

namespace Inspect

open Command in
@[scoped command_elab i]
def _root_.elabI : CommandElab
  | `(i| #i $t:term) => discard <| liftTermElabM <|
    withoutErrToSorry <| withSynthesize <| elabTerm t none
  | _ => throwUnsupportedSyntax

end Inspect
