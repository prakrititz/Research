# Derivation of verina_basic_71

kind: **loop**

- **loop** over state (idx : Nat), start (0)
  - invariant: `idx ≤ min str1.length str2.length ∧ str1.take idx = str2.take idx`
  - guard: `idx < min str1.length str2.length ∧ str1[idx]! = str2[idx]!`
  - variant: `min str1.length str2.length - idx`
  - result: `str1.take idx`
  - helper lemma `step71`: `∀ (l1 l2 : List Char) (idx : Nat), (idx ≤ min l1.length l2.length ∧ l1.take idx = l2.take idx) → (idx < min l1.length l2.length ∧ l1[idx]! = l2[idx]!) → (idx + 1 ≤ min l1.length l2.length ∧ l1.take (idx + 1) = l2.take (idx + 1))`
  - **term**: `idx + 1`
