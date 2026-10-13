# Derivation of he_121_solution

kind: **loop**

- **loop** over state (i : Nat, s : Int), start (0, 0)
  - invariant: `i ≤ lst.length ∧ s = (((List.range i).filter (fun j => j % 2 = 0 ∧ lst[j]! % 2 = 1)).map (fun j => lst[j]!)).sum`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `s`
  - **term**: `(i + 1, if i % 2 = 0 ∧ lst[i]! % 2 = 1 then s + lst[i]! else s)`
