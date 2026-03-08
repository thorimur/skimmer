module

import Skimmer.Working.Basic
import Skimmer.Refactor.Util.Ident

open Skimmer

-- currently we expect the module to be fed a single `RefactorArgs`
public def main (args : List String) : IO Unit :=
  IO.Main.refactorWithState args (·.readReplacements) refactorDeprecated.post
