-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findClosestElements_precond (numbers : List ℚ) : Prop :=
  -- !benchmark @start precond
  numbers.length ≥ 2
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findClosestElements (numbers : List ℚ) (h_precond : findClosestElements_precond (numbers)) : ℚ × ℚ :=
  -- !benchmark @start code
  let sorted := numbers.mergeSort (fun a b => a ≤ b)
  let pairs := sorted.zip sorted.tail
  pairs.foldl (fun best p => if p.2 - p.1 < best.2 - best.1 then p else best) pairs.head!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findClosestElements_postcond (numbers : List ℚ) (result: ℚ × ℚ) (h_precond : findClosestElements_precond (numbers)) :=
  -- !benchmark @start postcond
  (∃ j, j < numbers.length ∧ ∃ i, i < j ∧
      ((result.1 = numbers[i]! ∧ result.2 = numbers[j]!) ∨ (result.1 = numbers[j]! ∧ result.2 = numbers[i]!))) ∧
    result.1 ≤ result.2 ∧
    ∀ j, j < numbers.length → ∀ i, i < j → result.2 - result.1 ≤ |numbers[i]! - numbers[j]!|
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findClosestElements_spec_satisfied (numbers : List ℚ) (h_precond : findClosestElements_precond (numbers)) :
    findClosestElements_postcond (numbers) (findClosestElements (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
