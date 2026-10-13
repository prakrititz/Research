# Derivation of he_004_mean_absolute_deviation

kind: **loop**

- **bind** `m : ℚ` with property `m = numbers.sum / (numbers.length : ℚ)`
  - _value_:
    - **loop** over state (i : Nat, s : ℚ), start (0, 0)
      - invariant: `i ≤ numbers.length ∧ s = (numbers.take i).sum`
      - guard: `i < numbers.length`
      - variant: `numbers.length - i`
      - result: `s / (numbers.length : ℚ)`
      - **term**: `(i + 1, s + numbers[i]!)`
  - _continuation_:
    - **loop** over state (i : Nat, d : ℚ), start (0, 0)
      - invariant: `i ≤ numbers.length ∧ d = ((numbers.take i).map (fun x => |x - m|)).sum`
      - guard: `i < numbers.length`
      - variant: `numbers.length - i`
      - result: `d / (numbers.length : ℚ)`
      - **term**: `(i + 1, d + |numbers[i]! - m|)`
