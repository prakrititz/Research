# Derivation of he_043_pairs_sum_to_zero

kind: **loop**

- **loop** over state (j : Nat, found : Bool), start (0, false)
  - invariant: `j ≤ l.length ∧ (found = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ l[a]! + l[b]! = 0)`
  - guard: `j < l.length`
  - variant: `l.length - j`
  - result: `found`
  - **bind** `hit : Bool` with property `hit = true ↔ ∃ a, a < j ∧ l[a]! + l[j]! = 0`
    - _value_:
      - **loop** over state (i : Nat, seen : Bool), start (0, false)
        - invariant: `i ≤ j ∧ (seen = true ↔ ∃ a, a < i ∧ l[a]! + l[j]! = 0)`
        - guard: `i < j`
        - variant: `j - i`
        - result: `seen`
        - **term**: `(i + 1, seen || decide (l[i]! + l[j]! = 0))`
    - _continuation_:
      - **term**: `(j + 1, found || hit)`
