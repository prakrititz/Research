import Mathlib

@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse

@[reducible, simp]
def evenOddPalindrome_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def evenOddPalindrome_postcond (n : Nat) (result: Nat × Nat) (h_precond : evenOddPalindrome_precond (n)) :=
  result.1 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0)).length ∧
    result.2 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1)).length
