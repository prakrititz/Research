import Mathlib

def numOf (s : String) : Nat := (s.splitOn "/")[0]!.toNat!
def denOf (s : String) : Nat := (s.splitOn "/")[1]!.toNat!
@[reducible] def wellFormedFrac (s : String) : Prop := (s.splitOn "/").length = 2 ∧ (s.splitOn "/").all String.isNat = true ∧ 0 < denOf s

@[reducible, simp]
def simplify_precond (x : String) (n : String) : Prop :=
  wellFormedFrac x ∧ wellFormedFrac n

@[reducible, simp]
def simplify_postcond (x : String) (n : String) (result: Bool) (h_precond : simplify_precond (x) (n)) :=
  result = true ↔ (numOf x * numOf n) % (denOf x * denOf n) = 0
