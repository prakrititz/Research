import Mathlib

@[reducible, simp]
def search_precond (lst : List Nat) : Prop :=
  lst ≠ [] ∧ ∀ x ∈ lst, x > 0

@[reducible, simp]
def search_postcond (lst : List Nat) (result: Int) (h_precond : search_precond (lst)) :=
  (result = -1 ∧ ∀ x ∈ lst, lst.count x < x) ∨
    (result > 0 ∧ result.toNat ∈ lst ∧ lst.count result.toNat ≥ result.toNat ∧ ∀ x ∈ lst, lst.count x ≥ x → x ≤ result.toNat)
