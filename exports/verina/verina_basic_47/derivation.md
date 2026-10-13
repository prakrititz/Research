# Derivation of verina_basic_47

kind: **loop**

- **loop** over state (i : Nat, acc : Int), start (0, 0)
  - invariant: `i ≤ a.size ∧ acc = sumTo a i`
  - guard: `i < a.size`
  - variant: `a.size - i`
  - result: `acc`
  - helper lemma `sumTo_zero`: `∀ (a : Array Int), sumTo a 0 = 0`
  - helper lemma `sumTo_succ`: `∀ (a : Array Int) (i : Nat), sumTo a (i + 1) = sumTo a i + a[i]!`
  - **term**: `(i + 1, acc + a[i]!)`
