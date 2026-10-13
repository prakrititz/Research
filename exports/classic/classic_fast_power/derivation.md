# Derivation of classic_fast_power

kind: **loop**

- **loop** over state (acc : Int, base : Int, k : Nat), start (1, b, e)
  - invariant: `acc * base ^ k = b ^ e`
  - guard: `k > 0`
  - variant: `k`
  - result: `acc`
  - helper lemma `pow_odd_split`: `∀ (base : Int) (k : Nat), k % 2 = 1 → base ^ k = base * (base * base) ^ (k / 2)`
  - helper lemma `pow_even_split`: `∀ (base : Int) (k : Nat), k % 2 = 0 → base ^ k = (base * base) ^ (k / 2)`
  - **cases** on `k % 2 = 1`
    - _then_:
      - **term**: `(acc * base, base * base, k / 2)`
    - _else_:
      - **term**: `(acc, base * base, k / 2)`
