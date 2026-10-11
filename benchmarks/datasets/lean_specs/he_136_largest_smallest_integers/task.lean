-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def largestSmallestIntegers_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def largestSmallestIntegers (lst : List Int) (h_precond : largestSmallestIntegers_precond (lst)) : Option Int × Option Int :=
  -- !benchmark @start code
  ((lst.filter (fun x => x < 0)).max?, (lst.filter (fun x => x > 0)).min?)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def largestSmallestIntegers_postcond (lst : List Int) (result: Option Int × Option Int) (h_precond : largestSmallestIntegers_precond (lst)) :=
  -- !benchmark @start postcond
  ((result.1 = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ a ∈ lst, result.1 = some a ∧ a < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ a)) ∧
    ((result.2 = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ b ∈ lst, result.2 = some b ∧ 0 < b ∧ ∀ x ∈ lst, 0 < x → b ≤ x))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem largestSmallestIntegers_spec_satisfied (lst : List Int) (h_precond : largestSmallestIntegers_precond (lst)) :
    largestSmallestIntegers_postcond (lst) (largestSmallestIntegers (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
