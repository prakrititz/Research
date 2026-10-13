# Derivation of he_018_how_many_times

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ string.length ∧ acc = ((List.range i).filter (fun j => substring.toList.isPrefixOf (string.toList.drop j))).length`
  - guard: `i < string.length`
  - variant: `string.length - i`
  - result: `acc`
  - **term**: `(i + 1, if substring.toList.isPrefixOf (string.toList.drop i) then acc + 1 else acc)`
