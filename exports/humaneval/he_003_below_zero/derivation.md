# Derivation of he_003_below_zero

kind: **loop**

- **loop** over state (i : Nat, bal : Int, neg : Bool), start (0, 0, false)
  - invariant: `i ≤ operations.length ∧ bal = (operations.take i).sum ∧ (neg = true ↔ ∃ k, k ≤ i ∧ (operations.take k).sum < 0)`
  - guard: `i < operations.length`
  - variant: `operations.length - i`
  - result: `neg`
  - **term**: `(i + 1, bal + operations[i]!, neg || decide (bal + operations[i]! < 0))`
