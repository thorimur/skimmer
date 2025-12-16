module

import Skimmer.Refactor.Util.Ident -- TODO: use plugin instead

-- import deprecated decls:
import SkimmerTest.AccumulativeLinterTest.Deprecated.Basic

example : Nat := .constFoo

example : Nat := .foo .constFoo

example : Nat := Nat.constFoo

example : Nat := Nat.constFoo.foo
