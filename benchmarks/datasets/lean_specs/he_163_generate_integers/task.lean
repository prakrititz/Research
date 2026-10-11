-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def generateIntegers_precond (a : Nat) (b : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def generateIntegers (a : Nat) (b : Nat) (h_precond : generateIntegers_precond (a) (b)) : List Nat :=
  -- !benchmark @start code
  ((List.range (min (max a b + 1) 10 - min a b)).map (fun i => i + min a b)).filter (fun d => d % 2 == 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def generateIntegers_postcond (a : Nat) (b : Nat) (result: List Nat) (h_precond : generateIntegers_precond (a) (b)) :=
  -- !benchmark @start postcond
  (∀ i, i < result.length - 1 → result[i]! < result[i + 1]!) ∧ (∀ d ∈ result, d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b ∧ d < 10) ∧
    ∀ d, d < 10 → d % 2 = 0 → min a b ≤ d → d ≤ max a b → d ∈ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem generateIntegers_spec_satisfied (a : Nat) (b : Nat) (h_precond : generateIntegers_precond (a) (b)) :
    generateIntegers_postcond (a) (b) (generateIntegers (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
