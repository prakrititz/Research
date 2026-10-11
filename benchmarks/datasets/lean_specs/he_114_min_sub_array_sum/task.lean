-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minSubArraySum_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  nums ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minSubArraySum (nums : List Int) (h_precond : minSubArraySum_precond (nums)) : Int :=
  -- !benchmark @start code
  Id.run do
    let mut best := nums.head!
    let mut current : Int := 0
    for x in nums do
      current := min x (current + x)
      best := min best current
    return best
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minSubArraySum_postcond (nums : List Int) (result: Int) (h_precond : minSubArraySum_precond (nums)) :=
  -- !benchmark @start postcond
  (∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = result) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → result ≤ ((nums.drop i).take (j - i)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minSubArraySum_spec_satisfied (nums : List Int) (h_precond : minSubArraySum_precond (nums)) :
    minSubArraySum_postcond (nums) (minSubArraySum (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
