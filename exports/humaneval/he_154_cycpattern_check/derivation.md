# Derivation of he_154_cycpattern_check

kind: **loop**

- **loop** over state (i : Nat, found : Bool), start (0, false)
  - invariant: `i ≤ b.length ∧ (found = true ↔ ∃ k, k < i ∧ (b.toList.drop k ++ b.toList.take k) <:+: a.toList)`
  - guard: `i < b.length`
  - variant: `b.length - i`
  - result: `decide (b.length = 0) || found`
  - **term**: `(i + 1, found || decide ((b.toList.drop i ++ b.toList.take i) <:+: a.toList))`
