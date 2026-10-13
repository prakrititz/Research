import Mathlib

def ones (x : Int) : Nat := ((Nat.digits 2 x.natAbs).filter (fun d => d == 1)).length

@[reducible, simp]
def sortArray116_precond (arr : List Int) : Prop :=
  True

@[reducible, simp]
def sortArray116_postcond (arr : List Int) (result: List Int) (h_precond : sortArray116_precond (arr)) :=
  result.isPerm arr ∧ ∀ i, i < result.length - 1 → ones result[i]! < ones result[i + 1]! ∨ (ones result[i]! = ones result[i + 1]! ∧ result[i]! ≤ result[i + 1]!)
