import Mathlib

@[reducible, simp]
def evenOddCount_precond (num : Int) : Prop :=
  True

@[reducible, simp]
def evenOddCount_postcond (num : Int) (result: Nat × Nat) (h_precond : evenOddCount_precond (num)) :=
  result.1 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 0)).length ∧
    result.2 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length
