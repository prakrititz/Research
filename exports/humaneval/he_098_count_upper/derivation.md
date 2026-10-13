# Derivation of he_098_count_upper

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ s.length ∧ acc = ((List.range i).filter (fun j => j % 2 = 0 ∧ s.toList[j]! ∈ ['A', 'E', 'I', 'O', 'U'])).length`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `acc`
  - **term**: `(i + 1, if i % 2 = 0 ∧ s.toList[i]! ∈ ['A', 'E', 'I', 'O', 'U'] then acc + 1 else acc)`
