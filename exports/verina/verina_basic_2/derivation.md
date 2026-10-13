# Derivation of verina_basic_2

kind: **loop**

- **cases** on `s.size = 0`
  - _then_:
    - **term**: `none`
  - _else_:
    - **loop** over state (i : Nat, m : Nat), start (1, s[0]!)
      - invariant: `1 ≤ i ∧ i ≤ s.size ∧ (∃ j, j < i ∧ s[j]! = m) ∧ ∀ j, j < i → m ≤ s[j]!`
      - guard: `i < s.size`
      - variant: `s.size - i`
      - result: `some m`
      - **term**: `(i + 1, min m s[i]!)`
