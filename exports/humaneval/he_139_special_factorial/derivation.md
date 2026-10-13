# Derivation of he_139_special_factorial

kind: **loop**

- **loop** over state (i : Nat, fact : Nat, total : Nat), start (0, 1, 1)
  - invariant: `i ≤ n ∧ fact = factSpec i ∧ total = ((List.range i).map (fun j => factSpec (j + 1))).prod`
  - guard: `i < n`
  - variant: `n - i`
  - result: `total`
  - **term**: `(i + 1, fact * (i + 1), total * (fact * (i + 1)))`
