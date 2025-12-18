module

public import Lean.Data.NameMap
public import Lean.Elab.Command
import Lean

/-! # `local_linter`

This file adds a command of convenience for locally adding a linter (and allowing updates to it).
-/

open Lean Elab Term Command Linter

syntax localLinterDef := ident declVal
syntax localLinterClear := &"clear " (&"all" <|> ident)
syntax localLinterArgs := localLinterClear <|> localLinterDef

/--
`local_linter foo := fun stx => do ...` activates a linter on the current file. Note that the `declVal` is interpreted as the `run : CommandElab (:= Syntax → CommandElabM Unit)` field of a `Linter`, not a `Linter` declaration itself. All `declVal` syntax is allowed, such as match alts (``local_linter foo | `(command| ...) => ...``), `let rec`s and trailing `where`s.

`local_linter`s will persist even if the `local_linter` command is removed. Use `local_linter clear foo` or `local_linter clear all` to clear local linters.

To list which local linters are active, use `local_linter?`.
-/
syntax (name := localLinter) "local_linter " localLinterArgs : command

@[inherit_doc localLinter]
syntax "local_linter?" : command

open Parser.Command in
elab_rules : command
| `(command| local_linter $id:ident $val:declVal) => unsafe liftTermElabM <| do
  let name := id.getId ++ `localLinter
  let tempRunName := name ++ `run
  let type : Expr := mkConst ``CommandElab
  -- Instead of elaborating directly into an `Expr`, we use `#eval`'s approach to allow `let rec`s.
  let defView := mkDefViewOfDef { isUnsafe := true, visibility := .private } <|←
    `(definition| def $(mkIdentFrom id (`_root_ ++ tempRunName)) : $(← Term.exprToSyntax type) $val:declVal)
  -- Allow access to both `meta` and non-`meta` declarations as the compilation result does not
  -- escape the current module.
  withOptions (Compiler.compiler.checkMeta.set · false) do
    Term.elabMutualDef #[] { header := "" } #[defView]
  -- TODO: investigate why `local_linter foo := fun` reaches unreachable code;
  -- this is a hack that prevents that.
  -- TODO: handle potential internal error better
  if (← MonadLog.hasErrors) then return
  let tempRunName ← resolveGlobalConstNoOverload (mkIdentFrom val tempRunName)
  let some value := (← getConstInfo tempRunName).value?
    | throwErrorAt val "Internal error: run expression did not produce a value."
  let axioms ← value.getUsedConstants.mapM collectAxioms
  if axioms.any (·.contains ``sorryAx) then return

   -- TODO: correct `checkMeta`?
  let run ← evalConst CommandElab tempRunName (checkMeta := false)
  lintersRef.modify fun a => a.eraseP (·.name == name) |>.push { name, run }
| `(command| local_linter clear all) =>
  lintersRef.modify fun a => a.eraseP ((`localLinter).isSuffixOf ·.name)
| `(command| local_linter clear $name:ident) => do
  let erased ← lintersRef.modifyGet fun a =>
    match a.findFinIdx? (·.name == name.getId ++ `localLinter) with
    | none => (false, a)
    | some idx => (true, a.eraseIdx idx)
  unless erased do
    throwErrorAt name m!"No local linter {name} was found."
| `(command| local_linter?) => do
  let localLinters := (← lintersRef.get).filterMap (·.name.eraseSuffix? `localLinter)
  logInfo <| if localLinters.isEmpty then
    m!"No local linters have been declared." else m!"Local linters:\n{localLinters}"
