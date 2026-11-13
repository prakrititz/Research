/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
nums : List ℕ
k : ℕ
h_precond : longestGoodSubarray_precond nums k
⊢ longestGoodSubarray_postcond nums k
    (if nums = [] then 0
    else
      (List.map (fun arr => arr.length)
            (List.filter (fun arr => arr.all fun x => decide (x ≤ k))
              (List.map (fun arr => List.map (fun x => List.count x arr) arr)
                (List.flatMap
                  (fun start =>
                    List.map (fun len => List.take len (List.drop start nums)) (List.range (nums.length - start + 1)))
                  (List.range (nums.length + 1)))))).max?.get!)
    h_precond
-/
theorem probe (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond nums k) :
    longestGoodSubarray_postcond nums k (if nums = [] then 0 else (((((List.range (nums.length + 1)).flatMap (fun start => (List.range ((nums.length - start) + 1)).map (fun len => (nums.drop start).take len))).map (fun arr => arr.map (fun x => arr.count x))).filter (fun arr => arr.all (fun x => x ≤ k))).map (fun arr => arr.length)).max?.get!) h_precond := by
  sorry
