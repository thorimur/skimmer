module

import Skimmer.Util.LocalLinter
import Skimmer.Util.Inspect
import Batteries.Tactic.Alias
public meta import Skimmer.Lean.Elab.InfoTree

/-! # Ident Syntax

This module demonstrates the different sorts of identifier syntax.
-/

-- TODO: would be nice to have a widget display for infotrees which allowed us to selectively show, hide, and expand information.

set_option inspect true

open scoped Inspect

#check Lean.Elab.getDeclarationRange?

def Nat.c : Nat := 3
def Nat.foo : Nat → Nat := fun _ => 3

open Lean

local_linter foo := fun _ => do
  for t in ← Lean.Elab.getInfoTrees do
    let acc ← t.foldInfoM (init := #[]) fun ctx info acc => do
      let elaborator := info.toElabInfo?.map (·.elaborator) |>.getD `noElabInfo
      Lean.logInfo m!"{info.getKind}\
        @{if elaborator == Name.anonymous then m!"_" else m!"{elaborator}"}:\
        {format info.stx}{← if let .ofTermInfo ti := info then ctx.runMetaM ti.lctx (addMessageContextFull <| m!" => {ti.expr}{if ti.expr.isConst then " (const)" else if ti.expr.isFVar then " (fvar)" else ""}") else pure m!""}"
      let .ofTermInfo ti := info | return acc
      if ti.expr.isConstOf ``Nat.add then return acc.push ti.stx else return acc
    Lean.logInfo m!"{repr acc}"

-- ident
-- stx: single ident
-- info: `term[elabIdent|a.b] >- term[a], .. term[b]`; `.` ⊄ range (for either)
#i Nat.c.add

-- proj
-- stx: `Term.proj #[_, ".", id]`
-- info: `term[elabProj|e] >- term[e]`; `.` ⊄ e.range
-- Note that the syntax in the infotree is `identProj #[id]`
#i (3).add

-- dotIdent (`.c`)
-- stx: `Term.dotIdent #[".", id]`
-- info: `term[elabDotIdent|e] >- term[e]`; `.` ⊆ range [!]
#i (.c : Nat)

-- Here we have a dotIdent, but it's not recorded in the infotree (bug?)
-- The syntax range for `Nat.foo` covers the whole dotIdent, i.e. `.foo`.
-- It has no associated elaborator; not `elabIdent`, not `elabDotIdent`.
-- I suspect this is unintentional, given that the syntax is `Term.dotIdent`.

-- dotIdent application
-- stx: `Term.dotIdent #[".", id]` (same as above)
-- info: `term[e]`
#i (Nat.foo 4 : Nat)

-- This is not unique to dotIdents. The same goes for ordinary idents.

#i Nat.foo 4

-- Arguments are not subject to this issue. Perhaps we may therefore check only the heads of `elabApp`s instead of checking the expression of every `TermInfo`. But I'd like to be sure that getting the head always works as expected. We're safer going the check-every-expr route.

#i @Nat.foo

#i Nat.c |>.add

#i have : Nat.foo = Nat.foo := (by simp [Nat.foo]); true

open Nat in
#i foo

namespace Foo

set_option pp.fullNames true

def foo := 4

-- set_option pp.fullNames true
inductive Foo where
| yike

#i (3).foo

-- Note: `declId`s tend to be fvars.

@[deprecated foo (since := "yesterday")]
def bar := 4

alias bar' := foo

theorem foo_iff : True ↔ True := by rfl

alias ⟨fw, rev⟩ := foo_iff

#check ``foo

end Foo


public section exportNames

/- Exported names still resolve to the original name, but -/

set_option pp.fullNames true
namespace Gamma

def ray := true

end Gamma

namespace Light

export Gamma (ray)

#check ray
#check Light.ray
#check Gamma.ray

/-- warning: `ray -/
#guard_msgs (warning) in
run_elab logWarning m!"{repr <|← unresolveNameGlobal `ray}"

end Light

#check Light.ray

-- Note: `unresolveNameGlobal` does not check that the name actually resolves to the result if unknown.
-- Note: we are handling public declarations, but we would have to unresolve the full name `_private.<mod_name>.0.<name>` for it to "work" otherwise. I.e., this should (obviously)

#guard_msgs (error) in
#check Light.ray

/-- warning: `Gamma.ray -/
#guard_msgs (warning) in
run_elab logWarning m!"{repr <|← unresolveNameGlobal `Gamma.ray}"

open Gamma in
/-- warning: `ray -/
#guard_msgs (warning) in
run_elab logWarning m!"{repr <|← unresolveNameGlobal `Gamma.ray}"

open Light in
/-- warning: `ray -/
#guard_msgs (warning) in
run_elab logWarning m!"{repr <|← unresolveNameGlobal `Gamma.ray}"

namespace Light

/-- warning: `ray -/
#guard_msgs (warning) in
run_elab logWarning m!"{repr <|← unresolveNameGlobal `Gamma.ray}"

end Light

end exportNames


public section protectedNames

protected def Foo'.bar := fun _ : Bool => true

@[expose] def Foo' := Bool

-- Dot notation doesn't work
/--
error: Invalid field `bar`: The environment does not contain `Bool.bar`
  true
has type
  Bool
-/
#guard_msgs (error) in
#check (true).bar

def e : Foo' := false

@[expose] abbrev Foo'' := Bool

def e' : Foo'' := false

def Foo''.bar := fun _ : Bool => true

open Lean Elab Meta in
run_elab logInfo m!"{← withReducible <| isDefEqGuarded (mkConst ``Foo'') (mkConst ``Bool)}"
/--
error: Invalid field notation: Function `Foo''.bar` does not have a usable parameter of type `Foo''` for which to substitute `e'`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs (error) in
#check e'.bar

/--
error: Invalid field notation: Function `Foo'.bar` does not have a usable parameter of type `Foo'` for which to substitute `e`

Note: Such a parameter must be explicit, or implicit with a unique name, to be used by field notation
-/
#guard_msgs (error) in
#check e.bar

protected def Foo'.bar' := fun _ : Foo' => true

-- Protected defs may be used in dot notation without remaining protected:
#check e.bar'

-- unresolveName works as expected:
open Foo'
run_elab logWarning m!"{repr <|← unresolveNameGlobal `Foo'.bar}"


-- TODO: what about `PartialTerm`?

/-
Lean.Elab.App: `elabAppFn` is a nice catalog of possible syntax:
```
match f with
| `($(e).$idx:fieldIdx) => elabFieldIdx e idx explicit
| `($e |>.$idx:fieldIdx) => elabFieldIdx e idx explicit
| `($(e).$field:ident) => elabFieldName e field explicit
| `($e |>.$field:ident) => elabFieldName e field explicit
| `(@$(e).$idx:fieldIdx) => elabFieldIdx e idx (explicit := true)
| `(@$(e).$field:ident) => elabFieldName e field (explicit := true)
| `($_:ident@$_:term) =>
throwError m!"Expected a function, but found the named pattern{indentD f}"
++ .note m!"Named patterns `<identifier>@<term>` can only be used when pattern-matching"
| `($id:ident) => do
elabAppFnId id [] lvals namedArgs args expectedType? explicit ellipsis overloaded acc
| `($id:ident.{$us,*}) => do
let us ← elabExplicitUnivs us
elabAppFnId id us lvals namedArgs args expectedType? explicit ellipsis overloaded acc
| `(@$id:ident) =>
elabAppFn id lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
| `(@$_:ident.{$_us,*}) =>
elabAppFn (f.getArg 1) lvals namedArgs args expectedType? (explicit := true) ellipsis overloaded acc
| `(@$_)     => throwUnsupportedSyntax -- invalid occurrence of `@`
| `(_)       => throwError "A placeholder `_` cannot be used where a function is expected"
| `(.$id:ident) =>
let res ← withRef f <| resolveDottedIdentFn id id.getId.eraseMacroScopes expectedType?
-- Use (forceTermInfo := true) because we want to record the result of .ident resolution even in patterns
elabAppFnResolutions f res lvals namedArgs args expectedType? explicit ellipsis overloaded acc (forceTermInfo := true)
| _ => do

-/
