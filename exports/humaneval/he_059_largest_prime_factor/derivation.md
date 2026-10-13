# Derivation of he_059_largest_prime_factor

kind: **loop**

- **loop** over state (q : Nat), start (n)
  - invariant: `1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False`
  - guard: `1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)`
  - variant: `q`
  - result: `q`
  - helper lemma `lpf_exit`: `∀ (n q : Nat), n > 1 → (1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False) → ¬ (1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)) → (Nat.Prime q ∧ q ∣ n ∧ ∀ q2, q2 < n + 1 → Nat.Prime q2 → q2 ∣ n → q2 ≤ q)`
  - helper lemma `lpf_step`: `∀ (n q : Nat), (1 ≤ q ∧ q ≤ n ∧ ∀ r, r < n + 1 → q < r → Nat.Prime r → r ∣ n → False) → (1 < q ∧ ¬ (Nat.Prime q ∧ n % q = 0)) → (1 ≤ q - 1 ∧ q - 1 ≤ n ∧ ∀ r, r < n + 1 → q - 1 < r → Nat.Prime r → r ∣ n → False)`
  - **term**: `q - 1`
