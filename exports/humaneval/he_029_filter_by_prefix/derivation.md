# Derivation of he_029_filter_by_prefix

kind: **loop**

- **loop** over state (i : Nat, acc : List String), start (0, [])
  - invariant: `i ≤ strings.length ∧ acc = (strings.take i).filter (fun s => s.startsWith prefix_)`
  - guard: `i < strings.length`
  - variant: `strings.length - i`
  - result: `acc`
  - **term**: `(i + 1, if strings[i]!.startsWith prefix_ then acc ++ [strings[i]!] else acc)`
