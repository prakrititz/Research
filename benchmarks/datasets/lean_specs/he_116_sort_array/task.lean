-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def ones (x : Int) : Nat := ((Nat.digits 2 x.natAbs).filter (fun d => d == 1)).length
-- !benchmark @end precond_aux

@[reducible, simp]
def sortArray116_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortArray116 (arr : List Int) (h_precond : sortArray116_precond (arr)) : List Int :=
  -- !benchmark @start code
  arr.mergeSort (fun a b => decide (ones a < ones b) || (ones a == ones b && a ≤ b))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortArray116_postcond (arr : List Int) (result: List Int) (h_precond : sortArray116_precond (arr)) :=
  -- !benchmark @start postcond
  result.isPerm arr ∧ ∀ i, i < result.length - 1 → ones result[i]! < ones result[i + 1]! ∨ (ones result[i]! = ones result[i + 1]! ∧ result[i]! ≤ result[i + 1]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortArray116_spec_satisfied (arr : List Int) (h_precond : sortArray116_precond (arr)) :
    sortArray116_postcond (arr) (sortArray116 (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
