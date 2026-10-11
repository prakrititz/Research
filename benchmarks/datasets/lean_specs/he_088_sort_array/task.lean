-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sortArray88_precond (array : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortArray88 (array : List Nat) (h_precond : sortArray88_precond (array)) : List Nat :=
  -- !benchmark @start code
  if array = [] then [] else
    let asc := array.mergeSort (fun a b => a ≤ b)
    if (array.head! + array.getLast!) % 2 = 1 then asc else asc.reverse
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortArray88_postcond (array : List Nat) (result: List Nat) (h_precond : sortArray88_precond (array)) :=
  -- !benchmark @start postcond
  result.isPerm array ∧ (array ≠ [] → ((array.head! + array.getLast!) % 2 = 1 → ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!) ∧
      ((array.head! + array.getLast!) % 2 = 0 → ∀ i, i < result.length - 1 → result[i + 1]! ≤ result[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortArray88_spec_satisfied (array : List Nat) (h_precond : sortArray88_precond (array)) :
    sortArray88_postcond (array) (sortArray88 (array) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
