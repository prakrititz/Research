# Derivation of verina_advanced_73

kind: **loop**

- **loop** over state (v : Nat), start (0)
  - invariant: `∀ k, k < v → k ∈ l`
  - guard: `v ∈ l`
  - variant: `l.foldl max 0 + 1 - v`
  - result: `v`
  - helper lemma `foldl_max_nat`: `∀ (l : List Nat) (m : Nat), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l`
  - helper lemma `mem_le_max`: `∀ (s : List Nat) (v : Nat), v ∈ s → v ≤ s.foldl max 0`
  - **term**: `v + 1`
