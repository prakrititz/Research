/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
heights : List ℤ
h_precond : rain_precond heights
⊢ (if heights.length < 3 then 0
    else
      rain_postcond.sum_water heights
        (fun i => max 0 (min (rain_postcond.ml heights i 0 0) (rain_postcond.mr heights i 0) - heights[i]!)) 0 0) ≥
    0
-/
theorem probe (heights : List (Int)) (h_precond : rain_precond heights) :
    rain_postcond heights (if heights.length < 3 then 0 else rain_postcond.sum_water heights (fun i => max 0 ((min (rain_postcond.ml heights i 0 0) (rain_postcond.mr heights i 0)) - heights[i]!)) 0 0) h_precond := by
  sorry
