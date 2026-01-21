module

public meta import Lean

namespace Skimmer

open Lean Meta Elab Command Tactic TryThis

syntax "refactor" "deprecated" "all" : command

syntax "dive" ("prepare" ("execute")?)? : command

elab_rules : command
| `(refactor deprecated all) => pure ()

elab_rules : command
| `(command|dive%$tk) => liftCoreM <| do
    addSuggestion tk (header := "Prepare the following actions?\n\n  refactor deprecated all") (s := { suggestion := .string "prepare" })
| `(command|dive%$tk prepare%$p) => liftCoreM <| do
    addSuggestion (mkNullNode #[tk, p]) (header := "Prepared 6 refactors, 1 of which needs review. Apply refactors? the following dives?\n\n  refactor deprecated all") (s := { suggestion := .string "execute" })
| `(command|dive prepare execute) => pure ()
