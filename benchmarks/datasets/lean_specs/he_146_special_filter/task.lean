-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def firstDigit (n : Nat) : Nat := (toString n).toList.head!.toNat - 48
-- !benchmark @end precond_aux

@[reducible, simp]
def specialFilter_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def specialFilter (nums : List Int) (h_precond : specialFilter_precond (nums)) : Nat :=
  -- !benchmark @start code
  nums.foldl (fun acc x => if x > 10 && firstDigit x.natAbs % 2 == 1 && x.natAbs % 10 % 2 == 1 then acc + 1 else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def specialFilter_postcond (nums : List Int) (result: Nat) (h_precond : specialFilter_precond (nums)) :=
  -- !benchmark @start postcond
  result = (nums.filter (fun x => x > 10 ∧ firstDigit x.natAbs % 2 = 1 ∧ x.natAbs % 10 % 2 = 1)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem specialFilter_spec_satisfied (nums : List Int) (h_precond : specialFilter_precond (nums)) :
    specialFilter_postcond (nums) (specialFilter (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
