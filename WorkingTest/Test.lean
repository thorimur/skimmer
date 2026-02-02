
import Lean
import Batteries.Tactic.Alias

#check Bool.true

def Bar := Bool

@[deprecated Bar (since := "yesterday")] alias Foo := Bar

def Baz := Foo

def Foo.not (b : Foo) := Bool.not b

def Foo.notnot (b : Foo) := b.not.not

def Int.flipIf (b : Foo) (i : Int) : Int :=
  bif b then -i else i

@[deprecated Int.flipIf (since := "yesterday")]
def Foo.flipIf (b : Foo) (i : Int) : Int := i.flipIf b

example (b : Foo) : Int := b.flipIf (-3 : Int)

#check Foo
