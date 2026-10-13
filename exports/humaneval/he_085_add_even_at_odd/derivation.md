# Derivation of he_085_add_even_at_odd

kind: **loop**

- **loop** over state (i : Nat, s : Int), start (0, 0)
  - invariant: `i ≤ lst.length ∧ s = (((List.range i).filter (fun j => j % 2 = 1 ∧ lst[j]! % 2 = 0)).map (fun j => lst[j]!)).sum`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `s`
  - **term**: `(i + 1, if i % 2 = 1 ∧ lst[i]! % 2 = 0 then s + lst[i]! else s)`
