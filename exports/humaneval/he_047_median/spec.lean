import Mathlib

@[reducible, simp]
def median_precond (l : List ℚ) : Prop :=
  l ≠ []

@[reducible, simp]
def median_postcond (l : List ℚ) (result: ℚ) (h_precond : median_precond (l)) :=
  let s := l.mergeSort (fun a b => a ≤ b)
  |result - (if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2)| ≤ (1 / 1000000 : ℚ)
