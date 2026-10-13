# Derivation of verina_basic_9

kind: **loop**

- **loop** over state (i : Nat, f : Bool), start (0, false)
  - invariant: `i ≤ a.size ∧ (f = true ↔ ∃ k, k < i ∧ ∃ j, j < b.size ∧ a[k]! = b[j]!)`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `f`
  - **bind** `hit : Bool` with property `hit = true ↔ ∃ j, j < b.size ∧ a[i]! = b[j]!`
    - _value_:
      - **loop** over state (j : Nat, g : Bool), start (0, false)
        - invariant: `j ≤ b.size ∧ (g = true ↔ ∃ m, m < j ∧ a[i]! = b[m]!)`
        - guard: `j < b.size`
        - variant: `b.size - j`
        - result: `g`
        - **term**: `(j + 1, g || decide (a[i]! = b[j]!))`
    - _continuation_:
      - **term**: `(i + 1, f || hit)`
