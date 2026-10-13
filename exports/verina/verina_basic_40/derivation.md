# Derivation of verina_basic_40

kind: **loop**

- **bind** `m : Int` with property `(∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!`
  - helper lemma `exit40`: `∀ (s : Array Int) (m r : Int) (found : Bool) (i : Nat) (h : secondSmallest_precond s), ((∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!) → (i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ (found = false → ∀ k, k < i → s[k]! = m)) → ¬ i < s.size → secondSmallest_postcond s r h`
  - helper lemma `step40`: `∀ (s : Array Int) (m r : Int) (found : Bool) (i : Nat), ((∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!) → i < s.size → (i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ (found = false → ∀ k, k < i → s[k]! = m)) → (i + 1 ≤ s.size ∧ ((if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found) = true → (∃ idx, idx < i + 1 ∧ s[idx]! = (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r)) ∧ m < (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r) ∧ ∀ k, k < i + 1 → m < s[k]! → (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r) ≤ s[k]!) ∧ ((if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found) = false → ∀ k, k < i + 1 → s[k]! = m))`
  - _value_:
    - **loop** over state (i : Nat, m : Int), start (1, s[0]!)
      - invariant: `1 ≤ i ∧ i ≤ s.size ∧ (∃ idx, idx < i ∧ s[idx]! = m) ∧ ∀ k, k < i → m ≤ s[k]!`
      - guard: `i < s.size`
      - variant: `s.size - i`
      - result: `m`
      - **term**: `(i + 1, min m s[i]!)`
  - _continuation_:
    - **loop** over state (i : Nat, r : Int, found : Bool), start (0, 0, false)
      - invariant: `i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ (found = false → ∀ k, k < i → s[k]! = m)`
      - guard: `i < s.size`
      - variant: `s.size - i`
      - result: `r`
      - **term**: `(i + 1, if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r, if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found)`
