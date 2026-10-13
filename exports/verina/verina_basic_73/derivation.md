# Derivation of verina_basic_73

kind: **loop**

- **loop** over state (i : Nat, ok : Bool), start (0, true)
  - invariant: `i ≤ s.toList.length ∧ (ok = true ↔ ∀ k, k < i → (s.toList[k]! = p.toList[k]! ∨ p.toList[k]! = '?'))`
  - guard: `i < s.toList.length`
  - variant: `s.toList.length - i`
  - result: `ok`
  - **term**: `(i + 1, ok && decide (s.toList[i]! = p.toList[i]! ∨ p.toList[i]! = '?'))`
