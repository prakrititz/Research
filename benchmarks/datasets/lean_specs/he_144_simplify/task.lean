-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def numOf (s : String) : Nat := (s.splitOn "/")[0]!.toNat!
def denOf (s : String) : Nat := (s.splitOn "/")[1]!.toNat!
@[reducible] def wellFormedFrac (s : String) : Prop := (s.splitOn "/").length = 2 ∧ (s.splitOn "/").all String.isNat = true ∧ 0 < denOf s
-- !benchmark @end precond_aux

@[reducible, simp]
def simplify_precond (x : String) (n : String) : Prop :=
  -- !benchmark @start precond
  wellFormedFrac x ∧ wellFormedFrac n
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def simplify (x : String) (n : String) (h_precond : simplify_precond (x) (n)) : Bool :=
  -- !benchmark @start code
  decide ((numOf x * numOf n) % (denOf x * denOf n) = 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def simplify_postcond (x : String) (n : String) (result: Bool) (h_precond : simplify_precond (x) (n)) :=
  -- !benchmark @start postcond
  result = true ↔ (numOf x * numOf n) % (denOf x * denOf n) = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem simplify_spec_satisfied (x : String) (n : String) (h_precond : simplify_precond (x) (n)) :
    simplify_postcond (x) (n) (simplify (x) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
