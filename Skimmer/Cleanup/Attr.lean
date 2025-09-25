/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean
import Skimmer.AttrUtil

/-!
# Cleanup functionality

Provides an extensible way to run "cleanups" ("closeouts"?) at the end of every lean file. We do this by hijacking the elaboration of the end-of-input command that appears at the end of every file. Note that this usually just elaborates to `pure ()` (see `elabEoi`), so we are not preventing any crucial functionality.

Each cleanup has type `CommandElab`; the input `stx` is that of the `eoi` node itself.

TODO: make this scoped
-/

open Lean Meta Elab Command

-- TODO: seems like the wrong sort of thing, since we're always gathering them. Not that many, so maybe we should use an importedFn instead of scanning the whole array? or maybe a ref, like `addLinter` modifies?
initialize cleanupAttr : TagAttribute ← (registerTagAttribute
  `cleanup
  "Cleanup declarations which are run at the end of each file."
  (applicationTime := .afterCompilation)
  (validateHasExactlyTypeNoSorry <| mkConst ``CommandElab)
)
