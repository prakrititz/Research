/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
nums : List ℤ
h_precond : minSubArraySum_precond nums
⊢ ∃ j ≤ nums.length,
    ∃ i < j,
      (List.take (j - i) (List.drop i nums)).sum =
        List.foldl min nums[0]!
          (List.flatMap (fun j => List.map (fun i => (List.take (j - i) (List.drop i nums)).sum) (List.range j))
            (List.range (nums.length + 1)))

case right
nums : List ℤ
h_precond : minSubArraySum_precond nums
⊢ ∀ j ≤ nums.length,
    ∀ i < j,
      List.foldl min nums[0]!
          (List.flatMap (fun j => List.map (fun i => (List.take (j - i) (List.drop i nums)).sum) (List.range j))
            (List.range (nums.length + 1))) ≤
        (List.take (j - i) (List.drop i nums)).sum
-/
theorem probe (nums : List Int) (h_precond : minSubArraySum_precond nums) :
    minSubArraySum_postcond nums (List.foldl min nums[0]! ((List.range (nums.length + 1)).flatMap (fun j => (List.range j).map (fun i => ((nums.drop i).take (j - i)).sum)))) h_precond := by
  sorry
