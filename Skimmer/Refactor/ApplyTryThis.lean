/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

import Lean
public import Skimmer.Working.Cruft
public import Skimmer.Refactor.Edit
public meta import Lean.Elab.GuardMsgs

open Lean Meta Elab Command Skimmer Widget

partial def Lean.MessageData.getFirstWidget? (msg : MessageData)
    (filter : WidgetInstance → IO Bool := fun _ => pure true) : IO (Option WidgetInstance) := do
  match msg with
  | .ofFormatWithInfos _
  | .ofGoal _ => return none
  | .withContext _ msg
  | .withNamingContext _ msg
  | .group msg
  | .nest _ msg
  | .tagged _ msg => msg.getFirstWidget? filter
  | .trace _ _ _ => return none -- don't handle for now
  | .compose msg₁ msg₂ => do
    let some widget ← msg₁.getFirstWidget? filter | msg₂.getFirstWidget? filter
    return widget
  | .ofLazy f _ => do
    let d ← f none -- TODO: construct the PPContext, presumably by passing along `withContext` etc.
    let some msg := d.get? MessageData | return none
    msg.getFirstWidget? filter
  | .ofWidget wi _ => do if ← filter wi then return wi else return none

def Lean.MessageData.getFirstTextSuggestion? (msg : MessageData) :
    IO (Option <| Lsp.Range × String) := do
  let some wi ← msg.getFirstWidget? fun wi =>
      return wi.id == ``Hint.textInsertionWidget || wi.id == ``Hint.tryThisDiffWidget
    | return none
  let json := wi.props.run' {}
  let .ok range := json.getObjValAs? Lsp.Range "range" | return none
  let .ok newText := json.getObjValAs? String "suggestion" | return none
  return (range, newText)

-- Note: we can't look in the infotrees, as suggestions added by linters won't be there.
-- Assumes you only want to apply the first edit per message.
public def applyTryThis (edits : Array Edit) (_cmd : Syntax) : CommandElabM (Array Edit) := do
  let mut edits : Array Edit := edits
  for msg in (← waitForAllMessages).reportedPlusUnreported do
    let some (range, replacement) ← msg.data.getFirstTextSuggestion? | continue
    edits := edits.push { range := (← getFileMap).lspRangeToUtf8Range range, replacement }
  return edits
