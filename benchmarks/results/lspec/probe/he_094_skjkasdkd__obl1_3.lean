/- exit: on exit the invariant and the negated guard imply the postcondition
UNPROVED: no tactic of the cascade closes this

unsolved:
lst : List ℕ
best : ℕ
h_precond : skjkasdkd_precond lst
h1i :
  lst.length ≤ lst.length ∧
    (best = 0 ∨ ∃ k < lst.length, lst[k]! = best ∧ Nat.Prime best) ∧
      ∀ k < lst.length, Nat.Prime lst[k]! → lst[k]! ≤ best
h1g : ¬lst.length < lst.length
⊢ skjkasdkd_postcond lst (List.map (fun c => c.toNat - '0'.toNat) (toString best).toList).sum h_precond
-/
theorem probe (lst : List Nat) (i : Nat) (best : Nat) (h_precond : skjkasdkd_precond lst) (h1i : ((i ≤ lst.length) ∧ (((best = 0) ∨ (∃ k, (k < i) ∧ ((lst[k]! = best) ∧ (Nat.Prime best)))) ∧ (∀ k, (k < i) → ((Nat.Prime lst[k]!) → (lst[k]! ≤ best)))))) (h1g : ¬ (i < lst.length)) :
    skjkasdkd_postcond lst (((toString best).toList.map (fun c => c.toNat - '0'.toNat)).sum) h_precond := by
  sorry
