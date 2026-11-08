/- init: the invariant holds before the first iteration
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (numbers : List ℚ) (j : Nat) (lo : Rat) (hi : Rat) (h_precond : findClosestElements_precond numbers) (h1i : (((lo ≤ hi) ∧ ((∃ b, (b < j) ∧ (∃ a, (a < b) ∧ (((lo = numbers[a]!) ∧ (hi = numbers[b]!)) ∨ ((lo = numbers[b]!) ∧ (hi = numbers[a]!))))) ∧ (∀ b, (b < j) → (∀ a, (a < b) → ((hi - lo) ≤ |numbers[a]! - numbers[b]!|))))) ∧ ((2 ≤ j) ∧ (j ≤ numbers.length)))) (h1g : (j < numbers.length)) :
    (fun (i : Nat) (lo2 : Rat) (hi2 : Rat) => ((lo2 ≤ hi2) ∧ ((∃ b, (b < (j + 1)) ∧ (∃ a, (a < b) ∧ (((lo2 = numbers[a]!) ∧ (hi2 = numbers[b]!)) ∨ ((lo2 = numbers[b]!) ∧ (hi2 = numbers[a]!))))) ∧ ((∀ b, (b < j) → (∀ a, (a < b) → ((hi2 - lo2) ≤ |numbers[a]! - numbers[b]!|))) ∧ (∀ a, (a < i) → ((hi2 - lo2) ≤ |numbers[a]! - numbers[j]!|))))) ∧ (i ≤ j)) (0) (lo) (hi) := by
  sorry
