# Derivation of verina_advanced_39

kind: **loop**

- **loop** over state (i : Nat, m : Nat), start (1, lst[0]!)
  - invariant: `1 ≤ i ∧ i ≤ lst.length ∧ (∃ k, k < i ∧ lst[k]! = m) ∧ ∀ k, k < i → lst[k]! ≤ m`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `m`
  - **term**: `(i + 1, max m lst[i]!)`
