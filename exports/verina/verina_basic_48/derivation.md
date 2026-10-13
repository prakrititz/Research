# Derivation of verina_basic_48

kind: **loop**

- **bind** `r : Nat` with property `r * r ≤ n ∧ n < (r + 1) * (r + 1)`
  - _value_:
    - **loop** over state (r : Nat), start (0)
      - invariant: `r * r ≤ n`
      - guard: `(r + 1) * (r + 1) ≤ n`
      - variant: `n - r`
      - result: `r`
      - **term**: `r + 1`
  - _continuation_:
    - **term**: `decide (r * r = n)`
      - helper lemma `sq48`: `∀ (n r : Nat), (r * r ≤ n ∧ n < (r + 1) * (r + 1)) → (decide (r * r = n) = true ↔ ∃ i : Nat, i * i = n)`
      - helper lemma `sq48_ok`: `∀ (n r : Nat), (r * r ≤ n ∧ n < (r + 1) * (r + 1)) → isPerfectSquare_postcond n (decide (r * r = n))`
