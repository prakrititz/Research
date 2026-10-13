# Derivation of he_030_get_positive

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ l.length ∧ acc = (l.take i).filter (fun x => x > 0)`
  - guard: `i < l.length`
  - variant: `l.length - i`
  - result: `acc`
  - **term**: `(i + 1, if l[i]! > 0 then acc ++ [l[i]!] else acc)`
