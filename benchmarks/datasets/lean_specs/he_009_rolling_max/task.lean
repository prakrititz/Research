-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rollingMax_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rollingMax (numbers : List Int) (h_precond : rollingMax_precond (numbers)) : List Int :=
  -- !benchmark @start code
  (List.range numbers.length).map (fun i => (numbers.take (i + 1)).foldl max numbers[0]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rollingMax_postcond (numbers : List Int) (result: List Int) (h_precond : rollingMax_precond (numbers)) :=
  -- !benchmark @start postcond
  result.length = numbers.length ∧
    ∀ i, i < numbers.length → result[i]! ∈ numbers.take (i + 1) ∧ ∀ x ∈ numbers.take (i + 1), x ≤ result[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rollingMax_spec_satisfied (numbers : List Int) (h_precond : rollingMax_precond (numbers)) :
    rollingMax_postcond (numbers) (rollingMax (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
