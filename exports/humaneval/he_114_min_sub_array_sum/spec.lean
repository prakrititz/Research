import Mathlib

@[reducible, simp]
def minSubArraySum_precond (nums : List Int) : Prop :=
  nums ≠ []

@[reducible, simp]
def minSubArraySum_postcond (nums : List Int) (result: Int) (h_precond : minSubArraySum_precond (nums)) :=
  (∃ j, j ≤ nums.length ∧ ∃ i, i < j ∧ ((nums.drop i).take (j - i)).sum = result) ∧ ∀ j, j ≤ nums.length → ∀ i, i < j → result ≤ ((nums.drop i).take (j - i)).sum
