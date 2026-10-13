# Derivation of he_115_max_fill

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ grid.length ∧ acc = ((grid.take i).map (fun row => (row.sum + capacity - 1) / capacity)).sum`
  - guard: `i < grid.length`
  - variant: `grid.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc + (grid[i]!.sum + capacity - 1) / capacity)`
