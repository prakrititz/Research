# Derivation of verina_basic_43

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 0)
  - invariant: `i ≤ n ∧ 15 * acc = i * (2 * i + 1) * (7 + 24 * i^3 - 12 * i^2 - 14 * i)`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - helper lemma `step43`: `∀ (i acc : Nat), 15*acc = i*(2*i+1)*(7+24*i^3-12*i^2-14*i) → 15*(acc + (2*i+1)^4) = (i+1)*(2*(i+1)+1)*(7+24*(i+1)^3-12*(i+1)^2-14*(i+1))`
  - **term**: `(i + 1, acc + (2 * i + 1)^4)`
