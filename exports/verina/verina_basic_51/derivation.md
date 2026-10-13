# Derivation of verina_basic_51

kind: **loop**

- **loop** over state (i : Nat), start (0)
  - invariant: `i ≤ a.size ∧ ∀ k, k < i → a[k]! < key`
  - guard: `i < a.size ∧ a[i]! < key`
  - variant: `a.size - i`
  - result: `i`
  - helper lemma `exit51`: `∀ (a : Array Int) (key : Int) (i : Nat) (h : BinarySearch_precond a key), (i ≤ a.size ∧ ∀ k, k < i → a[k]! < key) → ¬ (i < a.size ∧ a[i]! < key) → BinarySearch_postcond a key i h`
  - **term**: `i + 1`
