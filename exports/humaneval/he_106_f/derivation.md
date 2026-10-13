# Derivation of he_106_f

kind: **loop**

- **loop** over state (i : Nat, acc : List Nat), start (0, [])
  - invariant: `i ≤ n ∧ acc = (List.range i).map (fun k => if (k + 1) % 2 = 0 then (k + 1).factorial else (k + 1) * (k + 2) / 2)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ [if (i + 1) % 2 = 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2])`
