# Derivation of he_083_starts_one_ends

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ 10 ^ n ∧ acc = ((List.range i).filter (fun m => 10 ^ (n - 1) ≤ m ∧ (m / 10 ^ (n - 1) = 1 ∨ m % 10 = 1))).length`
  - guard: `i < 10 ^ n`
  - variant: `10 ^ n - i`
  - result: `acc`
  - **term**: `(i + 1, if 10 ^ (n - 1) ≤ i ∧ (i / 10 ^ (n - 1) = 1 ∨ i % 10 = 1) then acc + 1 else acc)`
