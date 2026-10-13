# Derivation of he_035_max_element

kind: **loop**

- **loop** over state (i : Nat, m : Int), start (1, l.head!)
  - invariant: `1 ≤ i ∧ i ≤ l.length ∧ (∃ k, k < i ∧ l[k]! = m) ∧ ∀ k, k < i → l[k]! ≤ m`
  - guard: `i < l.length`
  - variant: `l.length - i`
  - result: `m`
  - **term**: `(i + 1, max m l[i]!)`
