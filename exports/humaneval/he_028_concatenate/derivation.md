# Derivation of he_028_concatenate

kind: **loop**

- **loop** over state (i : Nat, acc : String), start (0, "")
  - invariant: `i ≤ strings.length ∧ acc = String.join (strings.take i)`
  - guard: `i < strings.length`
  - variant: `strings.length - i`
  - result: `acc`
  - **term**: `(i + 1, acc ++ strings[i]!)`
