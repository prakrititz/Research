# Derivation of he_073_smallest_change

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ arr.length / 2 ∧ acc = ((List.range i).filter (fun k => arr[k]! ≠ arr[arr.length - 1 - k]!)).length`
  - guard: `i < arr.length / 2`
  - variant: `arr.length / 2 - i`
  - result: `acc`
  - **term**: `(i + 1, if arr[i]! ≠ arr[arr.length - 1 - i]! then acc + 1 else acc)`
