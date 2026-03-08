module

import Skimmer.Working.Basic
import Skimmer.Refactor.ApplyTryThis

open Skimmer

-- currently we expect the module to be fed a single `RefactorArgs`
public def main (args : List String) : IO Unit :=
  IO.Main.refactor args applyTryThis
