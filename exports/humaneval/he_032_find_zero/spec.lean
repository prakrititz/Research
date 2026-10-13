import Mathlib

def polyEval (xs : List Int) (x : ℚ) : ℚ := (List.range xs.length).foldl (fun acc i => acc + ((xs[i]! : Int) : ℚ) * x ^ i) 0

@[reducible, simp]
def findZero_precond (xs : List Int) : Prop :=
  xs ≠ [] ∧ xs.length % 2 = 0 ∧ xs.getLast! ≠ 0

@[reducible, simp]
def findZero_postcond (xs : List Int) (result: ℚ) (h_precond : findZero_precond (xs)) :=
  |polyEval xs result| < (1 / 10000 : ℚ)
