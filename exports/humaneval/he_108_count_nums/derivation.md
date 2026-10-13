# Derivation of he_108_count_nums

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ arr.length ∧ acc = ((arr.take i).filter (fun x => signedDigitSum x > 0)).length`
  - guard: `i < arr.length`
  - variant: `arr.length - i`
  - result: `acc`
  - **term**: `(i + 1, if signedDigitSum arr[i]! > 0 then acc + 1 else acc)`
