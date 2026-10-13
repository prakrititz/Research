import Mathlib

@[reducible, simp]
def skjkasdkd_precond (lst : List Nat) : Prop :=
  ∃ x ∈ lst, Nat.Prime x

@[reducible, simp]
def skjkasdkd_postcond (lst : List Nat) (result: Nat) (h_precond : skjkasdkd_precond (lst)) :=
  ∃ p ∈ lst, Nat.Prime p ∧ (∀ x ∈ lst, Nat.Prime x → x ≤ p) ∧ result = ((toString p).toList.map (fun c => c.toNat - '0'.toNat)).sum
