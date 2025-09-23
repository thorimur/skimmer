import SkimmerTest.AccumulativeLinterTest.SourceToRecord
import Skimmer.AttrUtil

open Lean

/-- info: [✅️SkimmerTest.AccumulativeLinterTest.SourceToRecord] -/
#guard_msgs in
run_cmd do logInfo m!"{recordSourceLinter.ext.getImportedEntries (← getEnv) |>.flatten}"
