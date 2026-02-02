
import Lean
import Batteries.Tactic.Alias

#check Bool.true

def Bar := Bool

@[deprecated Bar (since := "yesterday")] alias Foo := Bar

def Baz := Foo

def Foo.not (b : Foo) := Bool.not b

def Foo.notnot (b : Foo) := b.not.not

#check Foo
