# Derivation of he_066_digit_sum

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ s.length ∧ acc = (((s.toList.take i).filter Char.isUpper).map Char.toNat).sum`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `acc`
  - **term**: `(i + 1, if s.toList[i]!.isUpper then acc + s.toList[i]!.toNat else acc)`
