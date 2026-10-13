import Mathlib

@[reducible, simp]
def maxFill_precond (grid : List (List Nat)) (capacity : Nat) : Prop :=
  capacity ≥ 1

@[reducible, simp]
def maxFill_postcond (grid : List (List Nat)) (capacity : Nat) (result: Nat) (h_precond : maxFill_precond (grid) (capacity)) :=
  result = (grid.map (fun row => (row.sum + capacity - 1) / capacity)).sum
