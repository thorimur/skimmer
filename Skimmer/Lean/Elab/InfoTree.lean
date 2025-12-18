/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

import Lean
public import Lean.Message

namespace Lean.Elab

public section

/-- Tokens representing the different constructors of `Info`. -/
inductive InfoKind where
  | tacticInfo
  | termInfo
  | partialTermInfo
  | commandInfo
  | macroExpansionInfo
  | optionInfo
  | errorNameInfo
  | fieldInfo
  | completionInfo
  | userWidgetInfo
  | customInfo
  | fVarAliasInfo
  | fieldRedeclInfo
  | delabTermInfo
  | choiceInfo
  | docInfo
  | docElabInfo
  deriving Inhabited, Repr, DecidableEq

/-- The kind of an `Info` as a token. -/
def Info.getKind : Info → InfoKind
  | .ofTacticInfo _ => .tacticInfo
  | .ofTermInfo _ => .termInfo
  | .ofPartialTermInfo _ => .partialTermInfo
  | .ofCommandInfo _ => .commandInfo
  | .ofMacroExpansionInfo _ => .macroExpansionInfo
  | .ofOptionInfo _ => .optionInfo
  | .ofErrorNameInfo _ => .errorNameInfo
  | .ofFieldInfo _ => .fieldInfo
  | .ofCompletionInfo _ => .completionInfo
  | .ofUserWidgetInfo _ => .userWidgetInfo
  | .ofCustomInfo _ => .customInfo
  | .ofFVarAliasInfo _ => .fVarAliasInfo
  | .ofFieldRedeclInfo _ => .fieldRedeclInfo
  | .ofDelabTermInfo _ => .delabTermInfo
  | .ofChoiceInfo _ => .choiceInfo
  | .ofDocInfo _ => .docInfo
  | .ofDocElabInfo _ => .docElabInfo

instance : ToMessageData InfoKind where
  toMessageData
  | .tacticInfo => "[Tactic]"
  | .termInfo => "[Term]"
  | .partialTermInfo => "[PartialTerm]"
  | .commandInfo => "[Command]"
  | .macroExpansionInfo => "[MacroExpansion]"
  | .optionInfo => "[Option]"
  | .errorNameInfo => "[ErrorName]"
  | .fieldInfo => "[Field]"
  | .completionInfo => "[Completion]"
  | .userWidgetInfo => "[UserWidget]"
  | .customInfo => "[Custom]"
  | .fVarAliasInfo => "[FVarAlias]"
  | .fieldRedeclInfo => "[FieldRedecl]"
  | .delabTermInfo => "[DelabTerm]"
  | .choiceInfo => "[Choice]"
  | .docInfo => "[Doc]"
  | .docElabInfo => "[DocElab]"
