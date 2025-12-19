/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import SkimmerTest.AccumulativeLinterTest.SourceToRecord
public import Skimmer.AttrUtil

open Lean

/-- info: [✅️SkimmerTest.AccumulativeLinterTest.SourceToRecord] -/
#guard_msgs in
run_cmd do logInfo m!"{recordSourceLinter.ext.getImportedEntries (← getEnv) |>.flatten}"
