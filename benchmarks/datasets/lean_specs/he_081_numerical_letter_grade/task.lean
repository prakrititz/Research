-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def letterGrade (x : ℚ) : String :=
  if x = 4 then "A+" else if x > 37 / 10 then "A" else if x > 33 / 10 then "A-" else if x > 3 then "B+"
  else if x > 27 / 10 then "B" else if x > 23 / 10 then "B-" else if x > 2 then "C+" else if x > 17 / 10 then "C"
  else if x > 13 / 10 then "C-" else if x > 1 then "D+" else if x > 7 / 10 then "D" else if x > 0 then "D-" else "E"

-- !benchmark @end precond_aux

@[reducible, simp]
def numericalLetterGrade_precond (grades : List ℚ) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def numericalLetterGrade (grades : List ℚ) (h_precond : numericalLetterGrade_precond (grades)) : List String :=
  -- !benchmark @start code
  grades.map letterGrade
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def numericalLetterGrade_postcond (grades : List ℚ) (result: List String) (h_precond : numericalLetterGrade_precond (grades)) :=
  -- !benchmark @start postcond
  result.length = grades.length ∧ ∀ i, i < grades.length → result[i]! = letterGrade grades[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem numericalLetterGrade_spec_satisfied (grades : List ℚ) (h_precond : numericalLetterGrade_precond (grades)) :
    numericalLetterGrade_postcond (grades) (numericalLetterGrade (grades) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
