module

import Skimmer.Util.LocalLinter
import Skimmer.Util.Inspect

/-! # Ident Syntax

This module demonstrates the different sorts of identifier syntax
-/

set_option inspect true

def Nat.c : Nat := 3
def Nat.foo : Nat → Nat := fun _ => 3

local_linter foo := fun _ => do
  for t in ← Lean.Elab.getInfoTrees do
    let acc := t.foldInfo (init := #[]) fun _ info acc => Id.run do
      let .ofTermInfo ti := info | return acc
      if ti.expr.isConstOf ``Nat.add then return acc.push ti.stx else return acc
    Lean.logInfo m!"{repr acc}"

-- ident
-- stx: single ident
-- info: `term[elabIdent|a.b] >- term[a], .. term[b]`; `.` ⊄ range (for either)
/--
info: (i "#view" `Nat.c.add)
---
info: • [Command] @ ⟨50, 0⟩-⟨50, 15⟩ @ elabView
  • [Term] Nat.c.add : Nat → Nat @ ⟨50, 6⟩-⟨50, 15⟩ @ Lean.Elab.Term.elabIdent
    • [Completion-Id] Nat.c.add : none @ ⟨50, 6⟩-⟨50, 15⟩
    • [Term] Nat.c : Nat @ ⟨50, 6⟩-⟨50, 11⟩
    • [Completion-Dot] [Term] Nat.c : Nat @ ⟨50, 12⟩-⟨50, 15⟩ : none
    • [Term] Nat.add : Nat → Nat → Nat @ ⟨50, 12⟩-⟨50, 15⟩
---
info: #[Lean.Syntax.node
    (Lean.SourceInfo.none)
    `Lean.Parser.Term.identProj
    #[Lean.Syntax.ident
        (Lean.SourceInfo.original
          "".toRawSubstring
          { byteIdx := 1640 }
          "\n\n\n\n-- proj\n-- stx: `Term.proj #[_, \".\", id]`\n-- info: `term[elabProj|e] >- term[e]`; `.` ⊄ e.range\n-- Note that the syntax in the infotree is `identProj #[id]`\n".toRawSubstring
          { byteIdx := 1643 })
        "add".toRawSubstring
        `add
        []]]
-/
#guard_msgs in
#view Nat.c.add

-- proj
-- stx: `Term.proj #[_, ".", id]`
-- info: `term[elabProj|e] >- term[e]`; `.` ⊄ e.range
-- Note that the syntax in the infotree is `identProj #[id]`
/--
info: (i "#view" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (num "3") ")") "." `add))
---
info: • [Command] @ ⟨86, 0⟩-⟨86, 13⟩ @ elabView
  • [Term] Nat.add 3 : Nat → Nat @ ⟨86, 6⟩-⟨86, 13⟩ @ Lean.Elab.Term.elabProj
    • [Term] 3 : Nat @ ⟨86, 6⟩-⟨86, 9⟩ @ Lean.Elab.Term.expandParen
      • [MacroExpansion]
        (3)
        ===>
        3
        • [Term] 3 : Nat @ ⟨86, 7⟩-⟨86, 8⟩ @ Lean.Elab.Term.elabNumLit
    • [Completion-Dot] [Term] 3 : Nat @ ⟨86, 10⟩-⟨86, 13⟩ : some ?_uniq.9849
    • [Term] Nat.add : Nat → Nat → Nat @ ⟨86, 10⟩-⟨86, 13⟩
---
info: #[Lean.Syntax.node
    (Lean.SourceInfo.none)
    `Lean.Parser.Term.identProj
    #[Lean.Syntax.ident
        (Lean.SourceInfo.original
          "".toRawSubstring
          { byteIdx := 2933 }
          "\n\n-- dotIdent (`.c`)\n-- stx: `Term.dotIdent #[\".\", id]`\n-- info: `term[elabDotIdent|e] >- term[e]`; `.` ⊆ range [!]\n".toRawSubstring
          { byteIdx := 2936 })
        "add".toRawSubstring
        `add
        []]]
-/
#guard_msgs in
#view (3).add

-- dotIdent (`.c`)
-- stx: `Term.dotIdent #[".", id]`
-- info: `term[elabDotIdent|e] >- term[e]`; `.` ⊆ range [!]
/--
info: (i
 "#view"
 (Term.typeAscription (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (Term.dotIdent "." `c) ":" [`Nat] ")"))
---
info: • [Command] @ ⟨81, 0⟩-⟨81, 16⟩ @ elabView
  • [Term] Nat.c : Nat @ ⟨81, 6⟩-⟨81, 16⟩ @ Lean.Elab.Term.elabTypeAscription
    • [Term] Nat : Type @ ⟨81, 12⟩-⟨81, 15⟩ @ Lean.Elab.Term.elabIdent
      • [Completion-Id] Nat : some Sort.{?_uniq.10413} @ ⟨81, 12⟩-⟨81, 15⟩
      • [Term] Nat : Type @ ⟨81, 12⟩-⟨81, 15⟩
    • [Term] Nat.c : Nat @ ⟨81, 7⟩-⟨81, 9⟩ @ Lean.Elab.Term.elabDotIdent
      • [Completion] `c @ ⟨81, 8⟩-⟨81, 9⟩
      • [Term] Nat.c : Nat @ ⟨81, 7⟩-⟨81, 9⟩
---
info: #[]
-/
#guard_msgs in
#view (.c : Nat)

-- Here we have a dotIdent, but it's not recorded in the infotree (bug?)
-- The syntax range for `Nat.foo` covers the whole dotIdent, i.e. `.foo`.
-- It has no associated elaborator; not `elabIdent`, not `elabDotIdent`.
-- I suspect this is unintentional, given that the syntax is `Term.dotIdent`.

-- dotIdent application
-- stx: `Term.dotIdent #[".", id]` (same as above)
-- info: `term[e]`
/--
info: (i
 "#view"
 (Term.typeAscription
  (Term.hygienicLParen "(" (hygieneInfo `[anonymous]))
  (Term.app (Term.dotIdent "." `foo) [(num "4")])
  ":"
  [`Nat]
  ")"))
---
info: • [Command] @ ⟨112, 0⟩-⟨112, 20⟩ @ elabView
  • [Term] Nat.foo 4 : Nat @ ⟨112, 6⟩-⟨112, 20⟩ @ Lean.Elab.Term.elabTypeAscription
    • [Term] Nat : Type @ ⟨112, 16⟩-⟨112, 19⟩ @ Lean.Elab.Term.elabIdent
      • [Completion-Id] Nat : some Sort.{?_uniq.10414} @ ⟨112, 16⟩-⟨112, 19⟩
      • [Term] Nat : Type @ ⟨112, 16⟩-⟨112, 19⟩
    • [Term] Nat.foo 4 : Nat @ ⟨112, 7⟩-⟨112, 13⟩ @ Lean.Elab.Term.elabApp
      • [Completion] `foo @ ⟨112, 8⟩-⟨112, 11⟩
      • [Term] Nat.foo : Nat → Nat @ ⟨112, 7⟩-⟨112, 11⟩
      • [Term] 4 : Nat @ ⟨112, 12⟩-⟨112, 13⟩ @ Lean.Elab.Term.elabNumLit
---
info: #[]
-/
#guard_msgs in
#view (.foo 4 : Nat)

-- This is not unique to dotIdents. The same goes for ordinary idents.

/--
info: (i "#view" (Term.app `Nat.foo [(num "4")]))
---
info: • [Command] @ ⟨126, 0⟩-⟨126, 15⟩ @ elabView
  • [Term] Nat.foo 4 : Nat @ ⟨126, 6⟩-⟨126, 15⟩ @ Lean.Elab.Term.elabApp
    • [Completion-Id] Nat.foo : none @ ⟨126, 6⟩-⟨126, 13⟩
    • [Term] Nat.foo : Nat → Nat @ ⟨126, 6⟩-⟨126, 13⟩
    • [Term] 4 : Nat @ ⟨126, 14⟩-⟨126, 15⟩ @ Lean.Elab.Term.elabNumLit
---
info: #[]
-/
#guard_msgs in
#view Nat.foo 4

-- Arguments are not subject to this issue. Perhaps we may therefore check only the heads of `elabApp`s instead of checking the expression of every `TermInfo`. But I'd like to be sure that getting the head always works as expected. We're safer going the check-every-expr route.

/--
info: (i "#view" (Term.app `Nat.foo [`Nat.c]))
---
info: • [Command] @ ⟨142, 0⟩-⟨142, 19⟩ @ elabView
  • [Term] Nat.c.foo : Nat @ ⟨142, 6⟩-⟨142, 19⟩ @ Lean.Elab.Term.elabApp
    • [Completion-Id] Nat.foo : none @ ⟨142, 6⟩-⟨142, 13⟩
    • [Term] Nat.foo : Nat → Nat @ ⟨142, 6⟩-⟨142, 13⟩
    • [Term] Nat.c : Nat @ ⟨142, 14⟩-⟨142, 19⟩ @ Lean.Elab.Term.elabIdent
      • [Completion-Id] Nat.c : some Nat @ ⟨142, 14⟩-⟨142, 19⟩
      • [Term] Nat.c : Nat @ ⟨142, 14⟩-⟨142, 19⟩
---
info: #[]
-/
#guard_msgs in
#view Nat.foo Nat.c

-- `elabExplicit` is similar.

/--
info: (i "#view" (Term.explicit "@" `Nat.foo))
---
info: • [Command] @ ⟨155, 0⟩-⟨155, 14⟩ @ elabView
  • [Term] Nat.foo : Nat → Nat @ ⟨155, 6⟩-⟨155, 14⟩ @ Lean.Elab.Term.elabExplicit
    • [Completion-Id] Nat.foo : none @ ⟨155, 7⟩-⟨155, 14⟩
    • [Term] Nat.foo : Nat → Nat @ ⟨155, 7⟩-⟨155, 14⟩
---
info: #[]
-/
#guard_msgs in
#view @Nat.foo


/--
info: (i "#view" (Term.pipeProj `Nat.c "|>." `add []))
---
info: • [Command] @ ⟨176, 0⟩-⟨176, 18⟩ @ elabView
  • [Term] Nat.c.add : Nat → Nat @ ⟨176, 6⟩-⟨176, 18⟩ @ Lean.Elab.Term.elabPipeProj
    • [Completion-Id] Nat.c : none @ ⟨176, 6⟩-⟨176, 11⟩
    • [Term] Nat.c : Nat @ ⟨176, 6⟩-⟨176, 11⟩
    • [Completion-Dot] [Term] Nat.c : Nat @ ⟨176, 15⟩-⟨176, 18⟩ : none
    • [Term] Nat.add : Nat → Nat → Nat @ ⟨176, 15⟩-⟨176, 18⟩
---
info: #[Lean.Syntax.node
    (Lean.SourceInfo.none)
    `Lean.Parser.Term.identProj
    #[Lean.Syntax.ident
        (Lean.SourceInfo.original "".toRawSubstring { byteIdx := 6686 } "\n\n".toRawSubstring { byteIdx := 6689 })
        "add".toRawSubstring
        `add
        []]]
-/
#guard_msgs in
#view Nat.c |>.add

/--
warning: This simp argument is unused:
  Nat.foo

Hint: Omit it from the simp argument list.
  simp ̵[̵N̵a̵t̵.̵f̵o̵o̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
---
info: (i
 "#view"
 (Term.have
  "have"
  (Term.letConfig [])
  (Term.letDecl
   (Term.letIdDecl
    (Term.letId (hygieneInfo `[anonymous]))
    []
    [(Term.typeSpec ":" («term_=_» `Nat.foo "=" `Nat.foo))]
    ":="
    (Term.paren
     (Term.hygienicLParen "(" (hygieneInfo `[anonymous]))
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `Nat.foo)] "]"] [])])))
     ")")))
  ";"
  `true))
---
info: • [Command] @ ⟨225, 0⟩-⟨225, 59⟩ @ elabView
  • [Term] have this := ⋯;
    true : Bool @ ⟨225, 6⟩-⟨225, 59⟩ @ Lean.Elab.Term.elabHaveDecl
    • [Term] Nat.foo = Nat.foo : Prop @ ⟨225, 13⟩-⟨225, 30⟩ @ «_aux_Init_Notation___macroRules_term_=__2»
      • [MacroExpansion]
        Nat.foo = Nat.foo
        ===>
        binrel% Eq✝ Nat.foo Nat.foo
        • [Term] Nat.foo = Nat.foo : Prop @ ⟨225, 13⟩†-⟨225, 30⟩† @ Lean.Elab.Term.Op.elabBinRel
          • [Term] Nat.foo = Nat.foo : Prop @ ⟨225, 13⟩†-⟨225, 30⟩†
            • [Completion-Id] Eq✝ : none @ ⟨225, 13⟩†-⟨225, 30⟩†
            • [Term] Nat.foo : Nat → Nat @ ⟨225, 13⟩-⟨225, 20⟩ @ Lean.Elab.Term.elabIdent
              • [Completion-Id] Nat.foo : none @ ⟨225, 13⟩-⟨225, 20⟩
              • [Term] Nat.foo : Nat → Nat @ ⟨225, 13⟩-⟨225, 20⟩
            • [Term] Nat.foo : Nat → Nat @ ⟨225, 23⟩-⟨225, 30⟩ @ Lean.Elab.Term.elabIdent
              • [Completion-Id] Nat.foo : none @ ⟨225, 23⟩-⟨225, 30⟩
              • [Term] Nat.foo : Nat → Nat @ ⟨225, 23⟩-⟨225, 30⟩
    • [Tactic] @ ⟨225, 35⟩-⟨225, 52⟩
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `Nat.foo)] "]"] [])])))
      before ⏎
      ⊢ Nat.foo = Nat.foo
      after no goals
      • [Tactic] @ ⟨225, 35⟩-⟨225, 37⟩
        "by"
        before ⏎
        ⊢ Nat.foo = Nat.foo
        after no goals
        • [Tactic] @ ⟨225, 38⟩-⟨225, 52⟩ @ Lean.Elab.Tactic.evalTacticSeq
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `Nat.foo)] "]"] [])]))
          before ⏎
          ⊢ Nat.foo = Nat.foo
          after no goals
          • [Tactic] @ ⟨225, 38⟩-⟨225, 52⟩ @ Lean.Elab.Tactic.evalTacticSeq1Indented
            (Tactic.tacticSeq1Indented
             [(Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `Nat.foo)] "]"] [])])
            before ⏎
            ⊢ Nat.foo = Nat.foo
            after no goals
            • [Tactic] @ ⟨225, 38⟩-⟨225, 52⟩ @ Lean.Elab.Tactic.evalSimp
              (Tactic.simp "simp" (Tactic.optConfig []) [] [] ["[" [(Tactic.simpLemma [] [] `Nat.foo)] "]"] [])
              before ⏎
              ⊢ Nat.foo = Nat.foo
              after no goals
              • [Completion-Id] Nat.foo : none @ ⟨225, 44⟩-⟨225, 51⟩
              • [Term] Nat.foo : Nat → Nat @ ⟨225, 44⟩-⟨225, 51⟩
              • [Completion-Id] Nat.foo : none @ ⟨225, 44⟩-⟨225, 51⟩
              • [Term] Nat.foo : Nat → Nat @ ⟨225, 44⟩-⟨225, 51⟩
              • [CustomInfo(Lean.Elab.Tactic.UnusedSimpArgsInfo)]
    • [Term] this (isBinder := true) : Nat.foo = Nat.foo @ ⟨225, 11⟩†!-⟨225, 11⟩†!
    • [Term] true : Bool @ ⟨225, 55⟩-⟨225, 59⟩ @ Lean.Elab.Term.elabIdent
      • [Completion-Id] true : none @ ⟨225, 55⟩-⟨225, 59⟩
      • [Term] true : Bool @ ⟨225, 55⟩-⟨225, 59⟩
-/
#guard_msgs in
#view have : Nat.foo = Nat.foo := (by simp [Nat.foo]); true

/--
info: (Command.in (Command.open "open" (Command.openSimple [`Nat])) "in" (i "#view" `foo))
---
info: • [Command] @ ⟨247, 0⟩-⟨248, 9⟩ @ Lean.Elab.Command.expandInCmd
  • [MacroExpansion]
    open Nat in
    #view foo
    ===>
    failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)
    • [Command] @ ⟨247, 9⟩†-⟨247, 11⟩† @ Lean.Elab.Command.elabSection
    • [Command] @ ⟨247, 0⟩-⟨247, 8⟩ @ Lean.Elab.Command.elabOpen
    • [Command] @ ⟨1, 0⟩†-⟨1, 0⟩† @ Lean.Elab.Command.elabEndLocalScope
    • [Command] @ ⟨248, 0⟩-⟨248, 9⟩ @ elabView
      • [Term] foo : Nat → Nat @ ⟨248, 6⟩-⟨248, 9⟩ @ Lean.Elab.Term.elabIdent
        • [Completion-Id] foo : none @ ⟨248, 6⟩-⟨248, 9⟩
        • [Term] foo : Nat → Nat @ ⟨248, 6⟩-⟨248, 9⟩
    • [Command] @ ⟨247, 9⟩†-⟨247, 11⟩† @ Lean.Elab.Command.elabEnd
      • [Completion] (Command.end "end" []) @ ⟨247, 9⟩†-⟨247, 11⟩†
-/
#guard_msgs in
open Nat in
#view foo

/--
info: (i "#view" (Term.proj (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) (num "3") ")") "." `foo))
---
info: • [Command] @ ⟨265, 0⟩-⟨265, 13⟩ @ elabView
  • [Term] Nat.foo 3 : Nat @ ⟨265, 6⟩-⟨265, 13⟩ @ Lean.Elab.Term.elabProj
    • [Term] 3 : Nat @ ⟨265, 6⟩-⟨265, 9⟩ @ Lean.Elab.Term.expandParen
      • [MacroExpansion]
        (3)
        ===>
        3
        • [Term] 3 : Nat @ ⟨265, 7⟩-⟨265, 8⟩ @ Lean.Elab.Term.elabNumLit
    • [Completion-Dot] [Term] 3 : Nat @ ⟨265, 10⟩-⟨265, 13⟩ : some ?_uniq.121
    • [Term] Nat.foo : Nat → Nat @ ⟨265, 10⟩-⟨265, 13⟩
-/
#guard_msgs in
#view (3).foo

-- TODO: what about `PartialTerm`?
