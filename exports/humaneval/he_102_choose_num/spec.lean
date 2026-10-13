import Mathlib

@[reducible, simp]
def chooseNum_precond (x : Int) (y : Int) : Prop :=
  True

@[reducible, simp]
def chooseNum_postcond (x : Int) (y : Int) (result: Int) (h_precond : chooseNum_precond (x) (y)) :=
  (result = -1 ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 ≠ 0) ∨
    (result % 2 = 0 ∧ x ≤ result ∧ result ≤ y ∧ ∀ k, k < (y - x + 1).toNat → (x + (k : Int)) % 2 = 0 → x + (k : Int) ≤ result)
