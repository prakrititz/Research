# Derivation of he_133_sum_squares

kind: **loop**

- **loop** over state (i : Nat, acc : Int), start (0, 0)
  - invariant: `i ≤ lst.length ∧ acc = ((lst.take i).map (fun x => (⌈x⌉ : Int) * (⌈x⌉ : Int))).sum`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc + (⌈lst[i]!⌉ : Int) * (⌈lst[i]!⌉ : Int))`
