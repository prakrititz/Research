import Mathlib

@[reducible, simp]
def eat_precond (number : Nat) (need : Nat) (remaining : Nat) : Prop :=
  number ≤ 1000 ∧ need ≤ 1000 ∧ remaining ≤ 1000

@[reducible, simp]
def eat_postcond (number : Nat) (need : Nat) (remaining : Nat) (result: List Nat) (h_precond : eat_precond (number) (need) (remaining)) :=
  result.length = 2 ∧ result[0]! = number + min need remaining ∧ result[1]! = remaining - min need remaining
