-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def intersection_precond (interval1 : Int × Int) (interval2 : Int × Int) : Prop :=
  -- !benchmark @start precond
  interval1.1 ≤ interval1.2 ∧ interval2.1 ≤ interval2.2
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def intersection (interval1 : Int × Int) (interval2 : Int × Int) (h_precond : intersection_precond (interval1) (interval2)) : String :=
  -- !benchmark @start code
  let len := min interval1.2 interval2.2 - max interval1.1 interval2.1
  if len ≥ 2 && decide (Nat.Prime len.toNat) then "YES" else "NO"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def intersection_postcond (interval1 : Int × Int) (interval2 : Int × Int) (result: String) (h_precond : intersection_precond (interval1) (interval2)) :=
  -- !benchmark @start postcond
  let len := min interval1.2 interval2.2 - max interval1.1 interval2.1
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (len ≥ 2 ∧ Nat.Prime len.toNat))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem intersection_spec_satisfied (interval1 : Int × Int) (interval2 : Int × Int) (h_precond : intersection_precond (interval1) (interval2)) :
    intersection_postcond (interval1) (interval2) (intersection (interval1) (interval2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
