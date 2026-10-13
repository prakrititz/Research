import Mathlib

def firstDigit (n : Nat) : Nat := (toString n).toList.head!.toNat - 48

@[reducible, simp]
def specialFilter_precond (nums : List Int) : Prop :=
  True

@[reducible, simp]
def specialFilter_postcond (nums : List Int) (result: Nat) (h_precond : specialFilter_precond (nums)) :=
  result = (nums.filter (fun x => x > 10 ∧ firstDigit x.natAbs % 2 = 1 ∧ x.natAbs % 10 % 2 = 1)).length
