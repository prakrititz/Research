# Derivation of he_048_is_palindrome

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ text.length ∧ (ok = true ↔ ∀ k, k < i → text.toList[k]! = text.toList[text.length - 1 - k]!)`
  - guard: `i < text.length`
  - variant: `text.length - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (text.toList[i]! = text.toList[text.length - 1 - i]!))`
