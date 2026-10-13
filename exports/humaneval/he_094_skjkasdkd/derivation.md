# Derivation of he_094_skjkasdkd

kind: **loop**

- **loop** over state (i : Nat, best : Nat), start (0, 0)
  - invariant: `i ≤ lst.length ∧ (best = 0 ∨ ∃ k, k < i ∧ lst[k]! = best ∧ Nat.Prime best) ∧ ∀ k, k < i → Nat.Prime lst[k]! → lst[k]! ≤ best`
  - guard: `i < lst.length`
  - variant: `lst.length - i`
  - result: `((toString best).toList.map (fun c => c.toNat - '0'.toNat)).sum`
  - helper lemma `skj_exit`: `∀ (lst : List Nat) (best : Nat), (∃ x ∈ lst, Nat.Prime x) → (lst.length ≤ lst.length ∧ (best = 0 ∨ ∃ k, k < lst.length ∧ lst[k]! = best ∧ Nat.Prime best) ∧ ∀ k, k < lst.length → Nat.Prime lst[k]! → lst[k]! ≤ best) → ∃ p ∈ lst, Nat.Prime p ∧ (∀ x ∈ lst, Nat.Prime x → x ≤ p) ∧ ((toString best).toList.map (fun c => c.toNat - '0'.toNat)).sum = ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum`
  - **term**: `(i + 1, if Nat.Prime lst[i]! ∧ best < lst[i]! then lst[i]! else best)`
