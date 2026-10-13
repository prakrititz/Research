# Derivation of he_008_sum_product

kind: **loop**

- **loop** over state (i : Nat, s : Int, p : Int), start (0, 0, 1)
  - invariant: `i ≤ numbers.length ∧ s = (numbers.take i).sum ∧ p = (numbers.take i).prod`
  - guard: `i < numbers.length`
  - variant: `numbers.length - i`
  - result: `(s, p)`
  - **term**: `(i + 1, s + numbers[i]!, p * numbers[i]!)`
