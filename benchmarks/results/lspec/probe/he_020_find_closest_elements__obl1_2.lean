/- init: the invariant holds before the first iteration
UNPROVED: no tactic of the cascade closes this

unsolved:
case left.right.left
numbers : List ℚ
h_precond : findClosestElements_precond numbers
⊢ ∃ b < 2,
    ∃ a < b,
      min numbers[0]! numbers[1]! = numbers[a]! ∧ max numbers[0]! numbers[1]! = numbers[b]! ∨
        min numbers[0]! numbers[1]! = numbers[b]! ∧ max numbers[0]! numbers[1]! = numbers[a]!
-/
theorem probe (numbers : List ℚ) (h_precond : findClosestElements_precond numbers) :
    (fun (j : Nat) (lo : Rat) (hi : Rat) => ((lo ≤ hi) ∧ ((∃ b, (b < j) ∧ (∃ a, (a < b) ∧ (((lo = numbers[a]!) ∧ (hi = numbers[b]!)) ∨ ((lo = numbers[b]!) ∧ (hi = numbers[a]!))))) ∧ (∀ b, (b < j) → (∀ a, (a < b) → ((hi - lo) ≤ |numbers[a]! - numbers[b]!|))))) ∧ ((2 ≤ j) ∧ (j ≤ numbers.length))) (2) (min numbers[0]! numbers[1]!) (max numbers[0]! numbers[1]!) := by
  sorry
