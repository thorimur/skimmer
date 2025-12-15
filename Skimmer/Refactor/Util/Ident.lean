/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Skimmer.Refactor.Init

public meta section

open Skimmer Command Lean Meta Elab Term Command

def Lean.Name.matchesStemOf : Name → Name → Bool
| .str n₁ _, .str n₂ _ => n₁ == n₂
| _, _ => false

def Lean.Name.replaceLast : Name → String → Name
| .str n _, s => .str n s
| _, _ => .anonymous

/-- Like `foldInfoTree` but monadic -/
partial def Lean.Elab.InfoTree.foldInfoTreeM {m} [Monad m] (init : α) (f : ContextInfo → InfoTree → α → m α) : InfoTree → m α :=
  go none init
where
  go ctx? a
  | .context ctx t => go (ctx.mergeIntoOuter? ctx?) a t
  | t@(.node i ts) => do
    let a ← match ctx? with
      | none => pure a
      | some ctx => f ctx t a
    ts.foldlM (init := a) (go <| i.updateContext? ctx?)
  | .hole _ => pure a

open Parser Term in
-- TODO: consider factoring into general `replaceIdent` plus something like `replace : Syntax → CommandElabM Syntax`
def replaceDeprecatedIdent : Refactor where run stx := do
  let mut acc := #[]
  let env ← getEnv
  for t in ← getInfoTrees do
    -- TODO: could certainly traverse the tree more efficiently
    -- TODO: check sharing, should be ok, but...
    acc ← t.foldInfoM (init := acc) fun ctx info acc => do
      match info with
      | .ofTermInfo ti => do
      -- TODO: we can use `foldInfoTreesM` and just check nodes that are `elabApp`s, `elabIdent`s, `elabProj`s, `elabDotIdent`s, `elabExplicit`s...? (iirc). Should find out why `elabApp`s and `elabExplicit`s don't leave the usual info leaves.
      -- match info with
      -- | .node (.ofTermInfo ti) ch => do
      --   if ti.elaborator == ``elabApp then
      --     for c in ch do
      --       match c with
      --       | .node (.ofTermInfo ti) _ => do
              -- TODO: get original range, not just canonical
        let some (name, _) := ti.expr.const? | return acc -- continue
        let some newName := Linter.getDeprecatedNewName env name | return acc -- continue
        let some range := ti.stx.getRange? (canonicalOnly := true) | return acc -- continue
        -- Time to replace:
        trace[Skimmer.Refactor] "Updating {.ofConstName name} ↦ {.ofConstName newName}"
        let isSimpleEnough ← pure (newName.matchesStemOf name) <&&> liftTermElabM do
          withReducible <| isDefEq (← getConstInfo name).type (← getConstInfo newName).type
        unless isSimpleEnough do
          trace[Skimmer.Refactor] "Too complicated!\n  \
            {.ofConstName name} ↦ {.ofConstName newName} @ {range}"
          return acc -- continue
        -- TODO: generalize, un-`!` (valid since `matchesStemOf _ _ = true`)
        let last := newName.getString!
        -- TODO: don't assume `id` is a suffix of `name` necessarily
        -- TODO: more tracing in edge cases
        match ti.stx with
        | `(dotIdent|.$id:ident)
        | `(Term.ident|$id:ident) =>
          let some range := id.raw.getRange? true | return acc
          let newId := id.getId.replaceLast last
          if newId.isAnonymous then return acc else
            return acc.push {
              range
              replacement := newId.toString
            }
        | stx => do
          if stx.isOfKind identProjKind then
            let some range := stx.getRange? true | return acc
            let newId := stx[0].getId.replaceLast last
            return acc.push {
              range
              replacement := newId.toString
            }
          else
            return acc
        --   return acc
        -- else
        --   return acc
      | _ => return acc
  return acc

initialize addRefactor replaceDeprecatedIdent
