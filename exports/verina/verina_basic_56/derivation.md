# Derivation of verina_basic_56

kind: **loop**

- **loop** over state (i : Nat, r : Array Int), start (0, dest)
  - invariant: `i ≤ len ∧ r.size = dest.size ∧ (∀ k, k < dStart → r[k]! = dest[k]!) ∧ (∀ k, dStart + i ≤ k → k < r.size → r[k]! = dest[k]!) ∧ (∀ k, k < i → r[dStart + k]! = src[sStart + k]!)`
  - guard: `i < len`
  - variant: `len - i`
  - result: `r`
  - helper lemma `set_bang_get`: `∀ (r : Array Int) (p : Nat) (v : Int) (k : Nat), p < r.size → (r.set! p v)[k]! = if p = k then v else r[k]!`
  - helper lemma `step56`: `∀ (src dest r : Array Int) (sStart dStart len i : Nat), copy_precond src sStart dest dStart len → i < len → (i ≤ len ∧ r.size = dest.size ∧ (∀ k, k < dStart → r[k]! = dest[k]!) ∧ (∀ k, dStart + i ≤ k → k < r.size → r[k]! = dest[k]!) ∧ (∀ k, k < i → r[dStart + k]! = src[sStart + k]!)) → (i + 1 ≤ len ∧ (r.set! (dStart + i) src[sStart + i]!).size = dest.size ∧ (∀ k, k < dStart → (r.set! (dStart + i) src[sStart + i]!)[k]! = dest[k]!) ∧ (∀ k, dStart + (i + 1) ≤ k → k < (r.set! (dStart + i) src[sStart + i]!).size → (r.set! (dStart + i) src[sStart + i]!)[k]! = dest[k]!) ∧ (∀ k, k < i + 1 → (r.set! (dStart + i) src[sStart + i]!)[dStart + k]! = src[sStart + k]!))`
  - helper lemma `exit56`: `∀ (src dest r : Array Int) (sStart dStart len i : Nat) (h : copy_precond src sStart dest dStart len), (i ≤ len ∧ r.size = dest.size ∧ (∀ k, k < dStart → r[k]! = dest[k]!) ∧ (∀ k, dStart + i ≤ k → k < r.size → r[k]! = dest[k]!) ∧ (∀ k, k < i → r[dStart + k]! = src[sStart + k]!)) → ¬ i < len → copy_postcond src sStart dest dStart len r h`
  - **term**: `(i + 1, r.set! (dStart + i) src[sStart + i]!)`
