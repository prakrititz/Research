/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (n : Nat) (n2 : Nat) (d : Nat) (acc : List Nat) (h_precond : factorize_precond n) (h1i : ((1 ≤ n2) ∧ ((2 ≤ d) ∧ (((acc.prod * n2) = n) ∧ ((∀ p ∈ acc, (Nat.Prime p) ∧ (p < (d + 1))) ∧ ((∀ i, (i < (acc.length - 1)) → (acc[i]! ≤ acc[i + 1]!)) ∧ ((∀ k, (2 ≤ k) → ((k < d) → (¬ (k ∣ n2)))) ∧ ((n2 = 1) ∨ (d ≤ n2))))))))) (h1g : (1 < n2)) (h2 : ((n2 % d) = 0)) :
    (fun (n2 : Nat) (d : Nat) (acc : List Nat) => (1 ≤ n2) ∧ ((2 ≤ d) ∧ (((acc.prod * n2) = n) ∧ ((∀ p ∈ acc, (Nat.Prime p) ∧ (p < (d + 1))) ∧ ((∀ i, (i < (acc.length - 1)) → (acc[i]! ≤ acc[i + 1]!)) ∧ ((∀ k, (2 ≤ k) → ((k < d) → (¬ (k ∣ n2)))) ∧ ((n2 = 1) ∨ (d ≤ n2)))))))) (((n2 / d, d, acc ++ [d]))).1 (((n2 / d, d, acc ++ [d]))).2.1 (((n2 / d, d, acc ++ [d]))).2.2 ∧ (fun (n2 : Nat) (d : Nat) (acc : List Nat) => (n2 + n2) - d) (((n2 / d, d, acc ++ [d]))).1 (((n2 / d, d, acc ++ [d]))).2.1 (((n2 / d, d, acc ++ [d]))).2.2 < ((n2 + n2) - d) := by
  sorry
