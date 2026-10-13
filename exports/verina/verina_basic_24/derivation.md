# Derivation of verina_basic_24

kind: **loop**

- **bind** `ie : Nat` with property `ie < a.size ∧ isEven a[ie]! = true ∧ ∀ k, k < ie → isOdd a[k]! = true`
  - helper lemma `odd_not_even`: `∀ (n : Int), isOdd n = true → ¬ isEven n = true`
  - helper lemma `not_odd_even`: `∀ (n : Int), ¬ isOdd n = true → isEven n = true`
  - helper lemma `not_even_odd`: `∀ (n : Int), ¬ isEven n = true → isOdd n = true`
  - helper lemma `first_even_exit`: `∀ (a : Array Int) (n : Nat), (∃ x ∈ a, isEven x = true) → (n ≤ a.size ∧ ∀ k, k < n → isOdd a[k]! = true) → ¬ (n < a.size ∧ isOdd a[n]! = true) → (n < a.size ∧ isEven a[n]! = true ∧ ∀ k, k < n → isOdd a[k]! = true)`
  - helper lemma `first_odd_exit`: `∀ (a : Array Int) (n : Nat), (∃ x ∈ a, isOdd x = true) → (n ≤ a.size ∧ ∀ k, k < n → isEven a[k]! = true) → ¬ (n < a.size ∧ isEven a[n]! = true) → (n < a.size ∧ isOdd a[n]! = true ∧ ∀ k, k < n → isEven a[k]! = true)`
  - _value_:
    - **loop** over state (n : Nat), start (0)
      - invariant: `n ≤ a.size ∧ ∀ k, k < n → isOdd a[k]! = true`
      - guard: `n < a.size ∧ isOdd a[n]! = true`
      - variant: `a.size - n`
      - result: `n`
      - **term**: `n + 1`
  - _continuation_:
    - **bind** `jo : Nat` with property `jo < a.size ∧ isOdd a[jo]! = true ∧ ∀ k, k < jo → isEven a[k]! = true`
      - _value_:
        - **loop** over state (n : Nat), start (0)
          - invariant: `n ≤ a.size ∧ ∀ k, k < n → isEven a[k]! = true`
          - guard: `n < a.size ∧ isEven a[n]! = true`
          - variant: `a.size - n`
          - result: `n`
          - **term**: `n + 1`
      - _continuation_:
        - **term**: `a[ie]! - a[jo]!`
