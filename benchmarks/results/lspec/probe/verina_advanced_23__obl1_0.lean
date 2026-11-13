/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
n : ℤ
h_precond : isPowerOfTwo_precond n
⊢ isPowerOfTwo_postcond n
    (List.foldl (fun acc x => decide (acc = true ∨ pow 2 x = n ∧ n > 0)) false (List.range (n + 1).toNat)) h_precond
-/
theorem probe (n : Int) (h_precond : isPowerOfTwo_precond n) :
    isPowerOfTwo_postcond n ((List.range (n + 1).toNat).foldl (fun acc x => acc ∨ (((pow 2 x) = n) ∧ (n > 0))) false) h_precond := by
  sorry
