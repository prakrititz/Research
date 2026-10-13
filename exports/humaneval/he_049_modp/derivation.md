# Derivation of he_049_modp

kind: **loop**

- **loop** over state (i : Nat, acc : Nat), start (0, 1 % p)
  - invariant: `i ≤ n ∧ acc = 2 ^ i % p`
  - guard: `i < n`
  - variant: `n - i`
  - result: `acc`
  - helper lemma `pow_mod_step`: `∀ (i p : Nat), 2 ^ (i + 1) % p = 2 ^ i % p * 2 % p`
  - **term**: `(i + 1, acc * 2 % p)`
