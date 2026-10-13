import Mathlib

@[reducible, simp]
def exchange_precond (lst1 : List Int) (lst2 : List Int) : Prop :=
  True

@[reducible, simp]
def exchange_postcond (lst1 : List Int) (lst2 : List Int) (result: String) (h_precond : exchange_precond (lst1) (lst2)) :=
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (lst1.filter (fun x => x % 2 = 1)).length ≤ (lst2.filter (fun x => x % 2 = 0)).length)
