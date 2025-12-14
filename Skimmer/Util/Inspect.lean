module

public import Lean

open Lean Linter

/-! # Utilities for inspecting things -/

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

-- TODO: use `withSetOptionIn` when `#11313` lands.
def inspectLinter : Linter where
  run stx := do
    if ← getBoolOption `inspect.syntax <||> getBoolOption `inspect then
      if ← getBoolOption `inspect.syntax.repr then
        logInfo m!"{repr stx}"
      else
        logInfo m!"{stx}"
    if ← getBoolOption `inspect.syntax <||> getBoolOption `inspect then
      pure () -- TODO
