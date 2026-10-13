# Derivation of he_061_correct_bracketing

kind: **loop**

- **loop** over state (i : Nat, d : Int, ok : Bool), start (0, 0, true)
  - invariant: `i ≤ brackets.length ∧ d = ((brackets.toList.take i).count '(' : Int) - ((brackets.toList.take i).count ')' : Int) ∧ (ok = true ↔ ∀ k, k ≤ i → (brackets.toList.take k).count '(' ≥ (brackets.toList.take k).count ')')`
  - guard: `i < brackets.length`
  - variant: `brackets.length - i`
  - result: `ok && decide (d = 0)`
  - **term**: `(i + 1, d + (if brackets.toList[i]! = '(' then 1 else if brackets.toList[i]! = ')' then -1 else 0), ok && decide (d + (if brackets.toList[i]! = '(' then 1 else if brackets.toList[i]! = ')' then -1 else 0) ≥ 0))`
