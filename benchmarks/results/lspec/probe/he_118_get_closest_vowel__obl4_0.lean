/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (word : String) (i : Nat) (b : Option Nat) (h_precond : getClosestVowel_precond word) (h2i : ((i ≤ word.toList.length) ∧ (((b = none) ∧ (∀ j, (j < i) → (¬ (goodAt word.toList j)))) ∨ (∃ c, (b = (some c)) ∧ ((c < i) ∧ ((goodAt word.toList c) ∧ (∀ j, (j < i) → ((c < j) → (¬ (goodAt word.toList j)))))))))) (h2g : (i < word.toList.length)) :
    (fun (i : Nat) (b : Option Nat) => (i ≤ word.toList.length) ∧ (((b = none) ∧ (∀ j, (j < i) → (¬ (goodAt word.toList j)))) ∨ (∃ c, (b = (some c)) ∧ ((c < i) ∧ ((goodAt word.toList c) ∧ (∀ j, (j < i) → ((c < j) → (¬ (goodAt word.toList j))))))))) (((i + 1, if goodAt word.toList i then some i else b))).1 (((i + 1, if goodAt word.toList i then some i else b))).2 ∧ (fun (i : Nat) (b : Option Nat) => word.toList.length - i) (((i + 1, if goodAt word.toList i then some i else b))).1 (((i + 1, if goodAt word.toList i then some i else b))).2 < (word.toList.length - i) := by
  sorry
