# Derivation of he_007_filter_by_substring

kind: **loop**

- **loop** over state (i : Nat, acc : List String), start (0, [])
  - invariant: `i ≤ strings.length ∧ acc = (strings.take i).filter (fun s => decide (hasSub s substring))`
  - guard: `i < strings.length`
  - variant: `strings.length - i`
  - result: `acc`
  - **term**: `(i + 1, if decide (hasSub strings[i]! substring) then acc ++ [strings[i]!] else acc)`
