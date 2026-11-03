-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
inductive PyVal where
  | int (n : Int)
  | bool (b : Bool)
  | float (q : ℚ)
  | str (s : String)
  | none
  | list (l : List PyVal)
  | dict (d : List (PyVal × PyVal))
-- !benchmark @end precond_aux

@[reducible, simp]
def anyInt_precond (x : PyVal) (y : PyVal) (z : PyVal) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def anyInt (x : PyVal) (y : PyVal) (z : PyVal) (h_precond : anyInt_precond (x) (y) (z)) : Bool :=
  -- !benchmark @start code
  match x, y, z with
  | PyVal.int a, PyVal.int b, PyVal.int c => a == b + c || b == a + c || c == b + a
  | _, _, _ => false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def anyInt_postcond (x : PyVal) (y : PyVal) (z : PyVal) (result: Bool) (h_precond : anyInt_precond (x) (y) (z)) :=
  -- !benchmark @start postcond
  result = true ↔ (match x, y, z with
    | PyVal.int a, PyVal.int b, PyVal.int c => a = b + c ∨ b = a + c ∨ c = b + a
    | _, _, _ => False)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem anyInt_spec_satisfied (x : PyVal) (y : PyVal) (z : PyVal) (h_precond : anyInt_precond (x) (y) (z)) :
    anyInt_postcond (x) (y) (z) (anyInt (x) (y) (z) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
