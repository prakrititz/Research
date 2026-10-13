# Derivation of he_010_make_palindrome

kind: **loop**

- **loop** over state (i : Nat), start (0)
  - invariant: `i ≤ string.length ∧ ∀ j, j < i → ¬ isPal (string.toList.drop j)`
  - guard: `i < string.length ∧ ¬ isPal (string.toList.drop i)`
  - variant: `string.length - i`
  - result: `String.mk (string.toList ++ (string.toList.take i).reverse)`
  - helper lemma `mp_exit`: `∀ (s : String) (i : Nat), (i ≤ s.length ∧ ∀ j, j < i → ¬ isPal (s.toList.drop j)) → ¬ (i < s.length ∧ ¬ isPal (s.toList.drop i)) → ∃ i2, i2 ≤ s.length ∧ isPal (s.toList.drop i2) ∧ (∀ j, j < i2 → ¬ isPal (s.toList.drop j)) ∧ (String.mk (s.toList ++ (s.toList.take i).reverse)).toList = s.toList ++ (s.toList.take i2).reverse`
  - **term**: `i + 1`
