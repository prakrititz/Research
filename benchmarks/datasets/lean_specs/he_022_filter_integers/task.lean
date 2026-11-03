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
def filterIntegers_precond (values : List PyVal) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def filterIntegers (values : List PyVal) (h_precond : filterIntegers_precond (values)) : List Int :=
  -- !benchmark @start code
  values.foldr (fun v acc => match v with | PyVal.int n => n :: acc | _ => acc) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def filterIntegers_postcond (values : List PyVal) (result: List Int) (h_precond : filterIntegers_precond (values)) :=
  -- !benchmark @start postcond
  result = values.filterMap (fun v => match v with | PyVal.int n => some n | _ => none)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem filterIntegers_spec_satisfied (values : List PyVal) (h_precond : filterIntegers_precond (values)) :
    filterIntegers_postcond (values) (filterIntegers (values) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
