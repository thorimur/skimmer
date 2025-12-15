module

import SkimmerTest.AccumulativeLinterTest.Deprecated.Basic
import Skimmer.Refactor.Util.Ident -- TODO: make unnecessary via plugin

example : Nat := .constBar

example : Nat := .bar .constBar

example : Nat := Nat.constBar

example : Nat := Nat.constBar.bar
