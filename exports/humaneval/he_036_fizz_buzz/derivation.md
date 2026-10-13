# Derivation of he_036_fizz_buzz

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ n ∧ acc = (((List.range i).filter (fun j => j % 11 = 0 ∨ j % 13 = 0)).map (fun j => (toString j).toList.count '7')).sum`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - **term**: `(i + 1, if i % 11 = 0 ∨ i % 13 = 0 then acc + (toString i).toList.count '7' else acc)`
