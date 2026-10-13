# Derivation of verina_basic_46

kind: **loop**

- **loop** over state (i : Nat, pos : Int), start (0, -1)
  - invariant: `i ≤ arr.size ∧ (pos = -1 ∨ (0 ≤ pos ∧ pos.toNat < i ∧ arr[pos.toNat]! = elem)) ∧ (pos = -1 → ∀ k, k < i → arr[k]! ≠ elem) ∧ (0 ≤ pos → ∀ k, pos.toNat < k → k < i → arr[k]! ≠ elem)`
  - guard: `i < arr.size`
  - variant: `arr.size - i`
  - result: `pos`
  - helper lemma `exit46`: `∀ (arr : Array Int) (elem : Int) (i : Nat) (pos : Int) (h : lastPosition_precond arr elem), (i ≤ arr.size ∧ (pos = -1 ∨ (0 ≤ pos ∧ pos.toNat < i ∧ arr[pos.toNat]! = elem)) ∧ (pos = -1 → ∀ k, k < i → arr[k]! ≠ elem) ∧ (0 ≤ pos → ∀ k, pos.toNat < k → k < i → arr[k]! ≠ elem)) → ¬ i < arr.size → lastPosition_postcond arr elem pos h`
  - **term**: `(i + 1, if arr[i]! = elem then (i : Int) else pos)`
