import Mathlib

@[reducible, simp]
def isSimplePower_precond (x : Int) (n : Int) : Prop :=
  True

@[reducible, simp]
def isSimplePower_postcond (x : Int) (n : Int) (result: Bool) (h_precond : isSimplePower_precond (x) (n)) :=
  result = true ↔ (x = 1 ∨ ∃ k, k < x.natAbs + 3 ∧ 1 ≤ k ∧ n ^ k = x)
