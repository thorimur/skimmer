module

import SkimmerTest.AccumulativeLinterTest.Deprecated.Basic
import Skimmer.Refactor.Util.Ident -- TODO: make unnecessary via plugin

example : Nat := .constFoo

example : Nat := .foo .constFoo

example : Nat := Nat.constFoo

example : Nat := Nat.constFoo.foo
