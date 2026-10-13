# Derivation of he_026_remove_duplicates

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ numbers.length ∧ acc = (numbers.take i).filter (fun x => numbers.count x = 1)`
  - guard: `i < numbers.length`
  - variant: `numbers.length - i`
  - result: `acc`
  - **term**: `(i + 1, if numbers.count numbers[i]! = 1 then acc ++ [numbers[i]!] else acc)`
