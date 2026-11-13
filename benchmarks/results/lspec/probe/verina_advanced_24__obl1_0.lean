/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
nums : List ℤ
h_precond : lengthOfLIS_precond nums
⊢ ((List.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l) (lengthOfLIS_postcond.subsequences nums)).any
      fun l =>
      decide
        (↑l.length =
          ↑(List.foldl max 0
              (List.map List.length
                (List.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l)
                  (lengthOfLIS_postcond.subsequences nums)))))) =
    true

case right
nums : List ℤ
h_precond : lengthOfLIS_precond nums
⊢ ((List.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l) (lengthOfLIS_postcond.subsequences nums)).all
      fun l =>
      decide
        (↑l.length ≤
          ↑(List.foldl max 0
              (List.map List.length
                (List.filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l)
                  (lengthOfLIS_postcond.subsequences nums)))))) =
    true
-/
theorem probe (nums : List Int) (h_precond : lengthOfLIS_precond nums) :
    lengthOfLIS_postcond nums (let allIncreasing := (lengthOfLIS_postcond.subsequences nums).filter (fun l => lengthOfLIS_postcond.isStrictlyIncreasing l); (((allIncreasing.map List.length).foldl max 0 : Nat) : Int)) h_precond := by
  sorry
