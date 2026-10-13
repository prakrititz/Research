# Derivation of he_025_factorize

kind: **loop**

- **loop** over state (n2 : Nat, d : Nat, acc : List Nat), start (n, 2, [])
  - invariant: `(1 ≤ n2 ∧ 2 ≤ d ∧ (acc).prod * n2 = n ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n2) ∧ (n2 = 1 ∨ d ≤ n2))`
  - guard: `1 < n2`
  - variant: `n2 + n2 - d`
  - result: `acc`
  - helper lemma `fact_div`: `∀ (N n d : Nat) (acc : List Nat), (1 ≤ n ∧ 2 ≤ d ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n) ∧ (n = 1 ∨ d ≤ n)) → 1 < n → n % d = 0 → ((1 ≤ (n / d) ∧ 2 ≤ d ∧ ((acc ++ [d])).prod * (n / d) = N ∧ (∀ p ∈ (acc ++ [d]), Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < ((acc ++ [d])).length - 1 → ((acc ++ [d]))[i]! ≤ ((acc ++ [d]))[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ (n / d)) ∧ ((n / d) = 1 ∨ d ≤ (n / d))) ∧ ((n / d + n / d - d) < (n + n - d)))`
  - helper lemma `fact_nodiv`: `∀ (N n d : Nat) (acc : List Nat), (1 ≤ n ∧ 2 ≤ d ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < d + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < d → ¬ k ∣ n) ∧ (n = 1 ∨ d ≤ n)) → 1 < n → ¬ n % d = 0 → ((1 ≤ n ∧ 2 ≤ (d + 1) ∧ (acc).prod * n = N ∧ (∀ p ∈ acc, Nat.Prime p ∧ p < (d + 1) + 1) ∧ (∀ i, i < (acc).length - 1 → (acc)[i]! ≤ (acc)[i + 1]!) ∧ (∀ k, 2 ≤ k → k < (d + 1) → ¬ k ∣ n) ∧ (n = 1 ∨ (d + 1) ≤ n)) ∧ ((n + n - (d + 1)) < (n + n - d)))`
  - **cases** on `n2 % d = 0`
    - _then_:
      - **term**: `(n2 / d, d, acc ++ [d])`
    - _else_:
      - **term**: `(n2, d + 1, acc)`
