-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def evenOddCount_precond (num : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def evenOddCount (num : Int) (h_precond : evenOddCount_precond (num)) : Nat × Nat :=
  -- !benchmark @start code
  (toString num.natAbs).toList.foldl (fun (p : Nat × Nat) c => if (c.toNat - 48) % 2 == 0 then (p.1 + 1, p.2) else (p.1, p.2 + 1)) (0, 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def evenOddCount_postcond (num : Int) (result: Nat × Nat) (h_precond : evenOddCount_precond (num)) :=
  -- !benchmark @start postcond
  result.1 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 0)).length ∧
    result.2 = ((toString num.natAbs).toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem evenOddCount_spec_satisfied (num : Int) (h_precond : evenOddCount_precond (num)) :
    evenOddCount_postcond (num) (evenOddCount (num) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
