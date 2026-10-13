# Derivation of he_163_generate_integers

kind: **restate**

- **term**: `(List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))`
  - helper lemma `generate_ok`: `∀ (a b : Nat), (∀ i, i < ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))).length - 1 → ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))[i]! < ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))[i + 1]!) ∧ (∀ d ∈ ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b))), d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b ∧ d < 10) ∧ ∀ d, d < 10 → d % 2 = 0 → min a b ≤ d → d ≤ max a b → d ∈ ((List.range 10).filter (fun d => decide (d % 2 = 0 ∧ min a b ≤ d ∧ d ≤ max a b)))`
