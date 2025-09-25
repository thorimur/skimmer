/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
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
