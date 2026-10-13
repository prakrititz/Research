import Mathlib

@[reducible, simp]
def fizzBuzz_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def fizzBuzz_postcond (n : Nat) (result: Nat) (h_precond : fizzBuzz_precond (n)) :=
  result = (((List.range n).filter (fun i => i % 11 = 0 ∨ i % 13 = 0)).map (fun i => (toString i).toList.count '7')).sum
