import Mathlib

@[reducible, simp]
def sumSquaresCeil_precond (lst : List ℚ) : Prop :=
  True

@[reducible, simp]
def sumSquaresCeil_postcond (lst : List ℚ) (result: Int) (h_precond : sumSquaresCeil_precond (lst)) :=
  result = (lst.map (fun x => (⌈x⌉ : Int) * (⌈x⌉ : Int))).sum
