theorem probe (n : Nat) (i : Nat) (acc : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond n) (h1i : ((i ≤ n) ∧ ((15 * acc) = ((i * ((2 * i) + 1)) * (((7 + (24 * (i ^ 3))) - (12 * (i ^ 2))) - (14 * i)))))) (h1g : (i < n)) :
    (fun (i : Nat) (acc : Nat) => (i ≤ n) ∧ ((15 * acc) = ((i * ((2 * i) + 1)) * (((7 + (24 * (i ^ 3))) - (12 * (i ^ 2))) - (14 * i))))) (((i + 1, acc + (((2 * i) + 1) ^ 4)))).1 (((i + 1, acc + (((2 * i) + 1) ^ 4)))).2 ∧ (fun (i : Nat) (acc : Nat) => n - i) (((i + 1, acc + (((2 * i) + 1) ^ 4)))).1 (((i + 1, acc + (((2 * i) + 1) ^ 4)))).2 < (n - i) := by
  beta_reduce; obtain ⟨hi, h⟩ := h1i; refine ⟨⟨by omega, ?_⟩, by omega⟩
  have a1 : ∀ k : Nat, 12 * k ^ 2 ≤ 7 + 24 * k ^ 3 := fun k => by rcases k with _ | k <;> [simp; nlinarith [sq_nonneg k, pow_pos (Nat.succ_pos k) 3]]
  have a2 : ∀ k : Nat, 14 * k ≤ 7 + 24 * k ^ 3 - 12 * k ^ 2 := fun k => by have := a1 k; rcases k with _ | k <;> [simp; (zify [this]; nlinarith [sq_nonneg (k : Int), sq_nonneg ((k : Int) + 1)])]
  have b1 := a1 i; have b2 := a2 i; have c1 := a1 (i + 1); have c2 := a2 (i + 1)
  zify [b1, b2, c1, c2] at h ⊢; push_cast at h ⊢; nlinarith [h]
