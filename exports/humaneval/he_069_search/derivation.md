# Derivation of he_069_search

kind: **loop**

- **loop** over state (i : Nat, best : Int), start (0, -1)
  - invariant: `i ≤ lst.length ∧ ((best = -1 ∧ ∀ k, k < i → lst.count lst[k]! < lst[k]!) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ lst.count best.toNat ≥ best.toNat ∧ ∀ k, k < i → lst.count lst[k]! ≥ lst[k]! → lst[k]! ≤ best.toNat))`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `best`
  - helper lemma `search_exit`: `∀ (lst : List Nat) (best : Int), (lst.length ≤ lst.length ∧ ((best = -1 ∧ ∀ k, k < lst.length → lst.count lst[k]! < lst[k]!) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ lst.count best.toNat ≥ best.toNat ∧ ∀ k, k < lst.length → lst.count lst[k]! ≥ lst[k]! → lst[k]! ≤ best.toNat))) → ((best = -1 ∧ ∀ x ∈ lst, lst.count x < x) ∨ (best > 0 ∧ best.toNat ∈ lst ∧ lst.count best.toNat ≥ best.toNat ∧ ∀ x ∈ lst, lst.count x ≥ x → x ≤ best.toNat))`
  - **term**: `(i + 1, if lst.count lst[i]! ≥ lst[i]! ∧ (best = -1 ∨ best < (lst[i]! : Int)) then (lst[i]! : Int) else best)`
