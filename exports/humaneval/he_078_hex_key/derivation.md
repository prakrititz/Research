# Derivation of he_078_hex_key

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ num.length ∧ acc = ((num.toList.take i).filter (fun c => ['2', '3', '5', '7', 'B', 'D'].contains c)).length`
  - guard: `i < num.length`
  - variant: `num.length - i`
  - result: `acc`
  - **term**: `(i + 1, if ['2', '3', '5', '7', 'B', 'D'].contains num.toList[i]! then acc + 1 else acc)`
