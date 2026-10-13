import Mathlib

@[reducible, simp]
def getRow_precond (lst : List (List Int)) (x : Int) : Prop :=
  True

@[reducible, simp]
def getRow_postcond (lst : List (List Int)) (x : Int) (result: List (Nat × Nat)) (h_precond : getRow_precond (lst) (x)) :=
  (∀ p ∈ result, p.1 < lst.length ∧ p.2 < lst[p.1]!.length ∧ (lst[p.1]!)[p.2]! = x) ∧
    (∀ i, i < lst.length → ∀ j, j < lst[i]!.length → (lst[i]!)[j]! = x → (i, j) ∈ result) ∧ result.Nodup ∧
    ∀ k, k < result.length - 1 → result[k]!.1 < result[k + 1]!.1 ∨ (result[k]!.1 = result[k + 1]!.1 ∧ result[k + 1]!.2 < result[k]!.2)
