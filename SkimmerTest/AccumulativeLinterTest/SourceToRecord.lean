/- A comment preceding the header. -/

import SkimmerTest.AccumulativeLinterTest.RecordSource

import Lean

/-!
## Test
-/

def foo := 3

open Lean

/-- info: hello -/
#guard_msgs in
run_cmd logInfo "hello"
