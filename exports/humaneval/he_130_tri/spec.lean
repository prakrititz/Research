import Mathlib

@[reducible, simp]
def tri_precond (n : Nat) : Prop :=
  True

@[reducible, simp]
def tri_postcond (n : Nat) (result: List Nat) (h_precond : tri_precond (n)) :=
  result.length = n + 1 ∧ result[0]! = 1 ∧ (n ≥ 1 → result[1]! = 3) ∧
    ∀ i, i < n + 1 → 2 ≤ i → result[i]! = (if i % 2 = 0 then 1 + i / 2 else result[i - 1]! + result[i - 2]! + (1 + (i + 1) / 2))
