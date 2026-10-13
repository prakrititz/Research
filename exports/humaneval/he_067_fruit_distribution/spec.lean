import Mathlib

@[reducible, simp]
def fruitDistribution_precond (s : String) (n : Nat) : Prop :=
  let w := s.splitOn " "
  w.length ≥ 4 ∧ w[0]! ≠ "" ∧ w[3]! ≠ "" ∧ w[0]!.all Char.isDigit = true ∧ w[3]!.all Char.isDigit = true ∧ w[0]!.toNat! + w[3]!.toNat! ≤ n

@[reducible, simp]
def fruitDistribution_postcond (s : String) (n : Nat) (result: Nat) (h_precond : fruitDistribution_precond (s) (n)) :=
  let w := s.splitOn " "
  result = n - w[0]!.toNat! - w[3]!.toNat!
