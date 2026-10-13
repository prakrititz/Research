# Derivation of he_142_sum_squares

kind: **loop**

- **loop** over state (i : Nat, acc : Int), start (0, 0)
  - invariant: `i ≤ lst.length ∧ acc = ((List.range i).map (fun k => if k % 3 = 0 then lst[k]! ^ 2 else if k % 4 = 0 then lst[k]! ^ 3 else lst[k]!)).sum`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc + (if i % 3 = 0 then lst[i]! ^ 2 else if i % 4 = 0 then lst[i]! ^ 3 else lst[i]!))`
