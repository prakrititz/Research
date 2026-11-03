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

def lowerKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isLower && !s.toList.any Char.isUpper
  | _ => false

def upperKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isUpper && !s.toList.any Char.isLower
  | _ => false
-- !benchmark @end precond_aux

@[reducible, simp]
def checkDictCase_precond (keys : List PyVal) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def checkDictCase (keys : List PyVal) (h_precond : checkDictCase_precond (keys)) : Bool :=
  -- !benchmark @start code
  !keys.isEmpty && (keys.all lowerKey || keys.all upperKey)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def checkDictCase_postcond (keys : List PyVal) (result: Bool) (h_precond : checkDictCase_precond (keys)) :=
  -- !benchmark @start postcond
  result = true ↔ (keys ≠ [] ∧ (keys.all lowerKey = true ∨ keys.all upperKey = true))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem checkDictCase_spec_satisfied (keys : List PyVal) (h_precond : checkDictCase_precond (keys)) :
    checkDictCase_postcond (keys) (checkDictCase (keys) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
