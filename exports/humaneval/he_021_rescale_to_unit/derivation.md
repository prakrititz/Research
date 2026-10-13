# Derivation of he_021_rescale_to_unit

kind: **loop**

- **bind** `lo : ℚ` with property `lo = numbers.foldl min numbers[0]!`
  - _value_:
    - **loop** over state (i : Nat, m : ℚ), start (0, numbers[0]!)
      - invariant: `i ≤ numbers.length ∧ m = (numbers.take i).foldl min numbers[0]!`
      - guard: `i < numbers.length`
      - variant: `numbers.length - i`
      - result: `m`
      - **term**: `(i + 1, min m numbers[i]!)`
  - _continuation_:
    - **bind** `hi : ℚ` with property `hi = numbers.foldl max numbers[0]!`
      - _value_:
        - **loop** over state (i : Nat, m : ℚ), start (0, numbers[0]!)
          - invariant: `i ≤ numbers.length ∧ m = (numbers.take i).foldl max numbers[0]!`
          - guard: `i < numbers.length`
          - variant: `numbers.length - i`
          - result: `m`
          - **term**: `(i + 1, max m numbers[i]!)`
      - _continuation_:
        - **loop** over state (i : Nat, acc : List ℚ), start (0, [])
          - invariant: `i ≤ numbers.length ∧ acc = (numbers.take i).map (fun x => (x - lo) / (hi - lo))`
          - guard: `i < numbers.length`
          - variant: `numbers.length - i`
          - result: `acc`
          - **term**: `(i + 1, acc ++ [(numbers[i]! - lo) / (hi - lo)])`
