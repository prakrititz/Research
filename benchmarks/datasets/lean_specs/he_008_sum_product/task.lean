-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumProduct_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumProduct (numbers : List Int) (h_precond : sumProduct_precond (numbers)) : Int × Int :=
  -- !benchmark @start code
  (numbers.foldl (fun a x => a + x) 0, numbers.foldl (fun a x => a * x) 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumProduct_postcond (numbers : List Int) (result: Int × Int) (h_precond : sumProduct_precond (numbers)) :=
  -- !benchmark @start postcond
  result.1 = numbers.sum ∧ result.2 = numbers.prod
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumProduct_spec_satisfied (numbers : List Int) (h_precond : sumProduct_precond (numbers)) :
    sumProduct_postcond (numbers) (sumProduct (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
