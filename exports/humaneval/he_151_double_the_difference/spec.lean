import Mathlib

@[reducible, simp]
def doubleTheDifference_precond (lst : List (Int ⊕ ℚ)) : Prop :=
  True

@[reducible, simp]
def doubleTheDifference_postcond (lst : List (Int ⊕ ℚ)) (result: Int) (h_precond : doubleTheDifference_precond (lst)) :=
  result = (lst.map (Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0))).sum
