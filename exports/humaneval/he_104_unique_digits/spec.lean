import Mathlib

def noEvenDigit (n : Nat) : Bool := (toString n).toList.all (fun c => (c.toNat - 48) % 2 == 1)

@[reducible, simp]
def uniqueDigits_precond (x : List Nat) : Prop :=
  True

@[reducible, simp]
def uniqueDigits_postcond (x : List Nat) (result: List Nat) (h_precond : uniqueDigits_precond (x)) :=
  result.isPerm (x.filter noEvenDigit) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
