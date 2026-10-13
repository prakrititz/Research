import Mathlib

@[reducible, simp]
def changeBase_precond (x : Nat) (base : Nat) : Prop :=
  2 ≤ base ∧ base < 10

@[reducible, simp]
def changeBase_postcond (x : Nat) (base : Nat) (result: String) (h_precond : changeBase_precond (x) (base)) :=
  result.toList.all (fun c => c.isDigit && c.toNat - '0'.toNat < base) = true ∧
    result.toList.foldl (fun acc c => acc * base + (c.toNat - '0'.toNat)) 0 = x ∧
    (x = 0 → result = "0") ∧ (x > 0 → result.toList.head! ≠ '0')
