/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
nums : List ℤ
h_precond : majorityElement_precond nums
⊢ List.count (List.filter (fun x => decide (List.count x nums > nums.length / 2)) nums)[0]! nums > nums.length / 2

case right
nums : List ℤ
h_precond : majorityElement_precond nums
⊢ ∀ x ∈ nums,
    x ≠ (List.filter (fun x => decide (List.count x nums > nums.length / 2)) nums)[0]! →
      List.count x nums ≤ nums.length / 2
-/
theorem probe (nums : List Int) (h_precond : majorityElement_precond nums) :
    majorityElement_postcond nums ((nums.filter (fun x => (nums.count x) > (nums.length / 2)))[0]!) h_precond := by
  sorry
