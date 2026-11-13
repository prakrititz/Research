/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case right.left
nums : List ℤ
h_precond : FindSingleNumber_precond nums
⊢ (filterlist ((List.find? (fun x => decide (List.count x nums = 1)) nums).getD 0) nums).length = 1

case right.right
nums : List ℤ
h_precond : FindSingleNumber_precond nums
⊢ ∀ x ∈ nums, x = (List.find? (fun x => decide (List.count x nums = 1)) nums).getD 0 ∨ (filterlist x nums).length = 2
-/
theorem probe (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    FindSingleNumber_postcond nums ((nums.find? (fun x => decide ((nums.count x) = 1))).getD 0) h_precond := by
  sorry
