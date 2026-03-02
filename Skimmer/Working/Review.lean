/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean

namespace Skimmer

public section

syntax (name := reviewTermStx) "review% " "(" term " => " term ")" : term

-- NOW TODO: write in env extension
-- Hmm, maybe just import demo.lean in the dive file?
open Lean Meta Elab Term Tactic.TryThis
@[term_elab Skimmer.reviewTermStx] meta def elabReviewTerm : TermElab
  | stx@`(reviewTermStx| review% ($t₀:term => $t₁:term)), expectedType? => do
    -- NOW TODO: record stx somewhere
    let s ← withoutErrToSorry <| Term.observing <| withSynthesize <| elabTerm t₁ expectedType?
    match s with
    | .ok e s =>
      s.restore (restoreInfo := true)
      let suggestion : SuggestionText :=
        if let some s := t₁.raw.reprint then .string s else .tsyntax t₁
      let suggestion : Suggestion := {
        suggestion
      }
      addSuggestion stx suggestion
        (header := "Generated term is successful. Would you like to accept it?")
      return e
    | .error ex _ =>
      -- TODO(check): need to restore state for error?
      logWarningAt t₁ m!"Generated term failed with error:{indentD ex.toMessageData}"
    elabTerm t₀ expectedType?
  | _, _ => throwUnsupportedSyntax
