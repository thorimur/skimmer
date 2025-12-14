/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Skimmer.Refactor.Init

open Skimmer Command Lean Elab Term Command

/-- Like `foldInfoTree` but monadic-/
partial def Lean.Elab.InfoTree.foldInfoTreeM{m} [Monad m] (init : α) (f : ContextInfo → InfoTree → α → m α) : InfoTree → m α :=
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

-- TODO: consider factoring into general `replaceIdent` plus something like `replace : Syntax → CommandElabM Syntax`
def replaceDeprecatedIdent : Refactor where run stx := do
  let mut acc := #[]
  for t in ← getInfoTrees do
    -- TODO: could certainly traverse the tree more efficiently
    -- TODO: check sharing, should be ok, but...
    acc ← t.foldInfoTreeM (init := acc) fun ctx info acc => do
      match info with
      | .node (.ofTermInfo ti) ch =>
        unless ti.elaborator == ``elabIdent do
          return acc
        return acc
      | _ => return acc
  return acc
