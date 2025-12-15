module

public section

def Nat.bar : Nat → Nat := fun _ => 3

@[deprecated Nat.bar (since := "yesterday")]
def Nat.foo : Nat → Nat := fun _ => 3


def Nat.constBar : Nat := 3

@[deprecated Nat.constBar (since := "yesterday")]
def Nat.constFoo : Nat := 3
