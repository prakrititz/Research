-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def fruitDistribution_precond (s : String) (n : Nat) : Prop :=
  -- !benchmark @start precond
  let w := s.splitOn " "
  w.length ≥ 4 ∧ w[0]! ≠ "" ∧ w[3]! ≠ "" ∧ w[0]!.all Char.isDigit = true ∧ w[3]!.all Char.isDigit = true ∧ w[0]!.toNat! + w[3]!.toNat! ≤ n
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fruitDistribution (s : String) (n : Nat) (h_precond : fruitDistribution_precond (s) (n)) : Nat :=
  -- !benchmark @start code
  let w := s.splitOn " "
  n - w[0]!.toNat! - w[3]!.toNat!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fruitDistribution_postcond (s : String) (n : Nat) (result: Nat) (h_precond : fruitDistribution_precond (s) (n)) :=
  -- !benchmark @start postcond
  let w := s.splitOn " "
  result = n - w[0]!.toNat! - w[3]!.toNat!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fruitDistribution_spec_satisfied (s : String) (n : Nat) (h_precond : fruitDistribution_precond (s) (n)) :
    fruitDistribution_postcond (s) (n) (fruitDistribution (s) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
