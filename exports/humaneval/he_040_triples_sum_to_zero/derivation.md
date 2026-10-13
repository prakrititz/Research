# Derivation of he_040_triples_sum_to_zero

kind: **loop**

- **loop** over state (k : Nat, found : Bool), start (0, false)
  - invariant: `k ≤ l.length ∧ (found = true ↔ ∃ c, c < k ∧ ∃ b, b < c ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[c]! = 0)`
  - guard: `k < l.length`
  - variant: `l.length - k`
  - result: `found`
  - **bind** `hitk : Bool` with property `hitk = true ↔ ∃ b, b < k ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[k]! = 0`
    - _value_:
      - **loop** over state (j : Nat, fj : Bool), start (0, false)
        - invariant: `j ≤ k ∧ (fj = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[k]! = 0)`
        - guard: `j < k`
        - variant: `k - j`
        - result: `fj`
        - **bind** `hitj : Bool` with property `hitj = true ↔ ∃ a, a < j ∧ l[a]! + l[j]! + l[k]! = 0`
          - _value_:
            - **loop** over state (i : Nat, fi : Bool), start (0, false)
              - invariant: `i ≤ j ∧ (fi = true ↔ ∃ a, a < i ∧ l[a]! + l[j]! + l[k]! = 0)`
              - guard: `i < j`
              - variant: `j - i`
              - result: `fi`
              - **term**: `(i + 1, fi || decide (l[i]! + l[j]! + l[k]! = 0))`
          - _continuation_:
            - **term**: `(j + 1, fj || hitj)`
    - _continuation_:
      - **term**: `(k + 1, found || hitk)`
