import Mathlib

def letterGrade (x : ℚ) : String :=
  if x = 4 then "A+" else if x > 37 / 10 then "A" else if x > 33 / 10 then "A-" else if x > 3 then "B+"
  else if x > 27 / 10 then "B" else if x > 23 / 10 then "B-" else if x > 2 then "C+" else if x > 17 / 10 then "C"
  else if x > 13 / 10 then "C-" else if x > 1 then "D+" else if x > 7 / 10 then "D" else if x > 0 then "D-" else "E"

@[reducible, simp]
def numericalLetterGrade_precond (grades : List ℚ) : Prop :=
  True

@[reducible, simp]
def numericalLetterGrade_postcond (grades : List ℚ) (result: List String) (h_precond : numericalLetterGrade_precond (grades)) :=
  result.length = grades.length ∧ ∀ i, i < grades.length → result[i]! = letterGrade grades[i]!
