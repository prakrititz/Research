-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def circularShift_precond (x : Nat) (shift : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def circularShift (x : Nat) (shift : Nat) (h_precond : circularShift_precond (x) (shift)) : String :=
  -- !benchmark @start code
  let d := (toString x).toList
  let n := d.length
  String.mk (if shift > n then d.reverse else d.drop (n - shift % n) ++ d.take (n - shift % n))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def circularShift_postcond (x : Nat) (shift : Nat) (result: String) (h_precond : circularShift_precond (x) (shift)) :=
  -- !benchmark @start postcond
  let d := (toString x).toList
  let n := d.length
  result.toList = (if shift > n then d.reverse else d.drop (n - shift % n) ++ d.take (n - shift % n))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem circularShift_spec_satisfied (x : Nat) (shift : Nat) (h_precond : circularShift_precond (x) (shift)) :
    circularShift_postcond (x) (shift) (circularShift (x) (shift) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
