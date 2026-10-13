# Derivation of verina_basic_7

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ n ∧ 3 * acc = i * (2 * i - 1) * (2 * i + 1)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - helper lemma `step7`: `∀ (i acc : Nat), 3*acc = i*(2*i-1)*(2*i+1) → 3*(acc + (2*i+1)*(2*i+1)) = (i+1)*(2*(i+1)-1)*(2*(i+1)+1)`
  - **term**: `(i + 1, acc + (2 * i + 1) * (2 * i + 1))`
