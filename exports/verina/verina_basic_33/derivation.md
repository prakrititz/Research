# Derivation of verina_basic_33

kind: **loop**

- **loop** over state (v : Nat), start (0)
  - invariant: `∀ k, k < v → List.elem k s = true`
  - guard: `List.elem v s = true`
  - variant: `s.foldl max 0 + 1 - v`
  - result: `v`
  - helper lemma `foldl_max_nat`: `∀ (l : List Nat) (m : Nat), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l`
  - helper lemma `elem_le_max`: `∀ (s : List Nat) (v : Nat), List.elem v s = true → v ≤ s.foldl max 0`
  - **term**: `v + 1`
