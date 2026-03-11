/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

import Skimmer.Working.Basic
import Skimmer.Refactor.ApplyTryThis

open Skimmer

-- currently we expect the module to be fed a single `RefactorArgs`
public def main (args : List String) : IO Unit :=
  IO.Main.refactor args applyTryThis
