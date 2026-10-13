# Derivation of he_064_vowels_count

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ s.length ∧ acc = ((s.toList.take i).filter (fun c => ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)).length`
  - guard: `i < s.length`
  - variant: `s.length - i`
  - result: `acc + (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0)`
  - **term**: `(i + 1, if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains s.toList[i]! then acc + 1 else acc)`
