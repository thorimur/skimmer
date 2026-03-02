
import Lean
import Batteries.Tactic.Alias

def Int.isPos  (i : Int) : Bool := 0 < i

@[deprecated Int.isPos (since := "yesterday")]
alias Bool.isPos := Int.isPos

example (j : Int) : Bool :=
  .isPos j
