# Derivation of he_000_has_close_elements

kind: **loop**

- **loop** over state (j : Nat, found : Bool), start (0, false)
  - invariant: `j ≤ numbers.length ∧ (found = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ |numbers[a]! - numbers[b]!| < threshold)`
  - guard: `j < numbers.length`
  - variant: `numbers.length - j`
  - result: `found`
  - **bind** `hit : Bool` with property `hit = true ↔ ∃ a, a < j ∧ |numbers[a]! - numbers[j]!| < threshold`
    - _value_:
      - **loop** over state (i : Nat, seen : Bool), start (0, false)
        - invariant: `i ≤ j ∧ (seen = true ↔ ∃ a, a < i ∧ |numbers[a]! - numbers[j]!| < threshold)`
        - guard: `i < j`
        - variant: `j - i`
        - result: `seen`
        - **term**: `(i + 1, seen || decide (|numbers[i]! - numbers[j]!| < threshold))`
    - _continuation_:
      - **term**: `(j + 1, found || hit)`
