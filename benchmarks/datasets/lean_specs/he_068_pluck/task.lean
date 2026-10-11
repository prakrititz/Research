-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def pluck_precond (arr : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def pluck (arr : List Nat) (h_precond : pluck_precond (arr)) : List Nat :=
  -- !benchmark @start code
  let evens := arr.filter (fun x => x % 2 == 0)
  if evens.isEmpty then [] else
    let m := evens.foldl min evens.head!
    [m, arr.idxOf m]
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def pluck_postcond (arr : List Nat) (result: List Nat) (h_precond : pluck_precond (arr)) :=
  -- !benchmark @start postcond
  (result = [] ↔ ∀ x ∈ arr, x % 2 = 1) ∧
    (result ≠ [] → result.length = 2 ∧ result[1]! < arr.length ∧ arr[result[1]!]! = result[0]! ∧ result[0]! % 2 = 0 ∧
      (∀ x ∈ arr, x % 2 = 0 → result[0]! ≤ x) ∧ ∀ j, j < result[1]! → arr[j]! ≠ result[0]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem pluck_spec_satisfied (arr : List Nat) (h_precond : pluck_precond (arr)) :
    pluck_postcond (arr) (pluck (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
