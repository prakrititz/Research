# Derivation of classic_reverse

kind: **loop**

- **loop** over state (i : Nat, acc : List Int), start (0, [])
  - invariant: `i ≤ l.length ∧ acc = (l.take i).reverse`
  - guard: `i < l.length`
  - variant: `l.length - i`
  - result: `acc`
  - helper lemma `rev_getBang`: `∀ (l : List Int) (i : Nat), i < l.length → l.reverse[i]! = l[l.length - 1 - i]!`
  - **term**: `(i + 1, l[i]! :: acc)`
