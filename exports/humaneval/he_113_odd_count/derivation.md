# Derivation of he_113_odd_count

kind: **loop**

- **loop** over state (i : Nat, acc : List String), start (0, [])
  - invariant: `i ≤ lst.length ∧ acc = (List.range i).map (fun k => oddMsg (oddDigits lst[k]!))`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [oddMsg (oddDigits lst[i]!)])`
