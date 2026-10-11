-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumSquaresCeil_precond (lst : List ℚ) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumSquaresCeil (lst : List ℚ) (h_precond : sumSquaresCeil_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.foldl (fun (acc : Int) x => acc + (⌈x⌉ : Int) * (⌈x⌉ : Int)) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumSquaresCeil_postcond (lst : List ℚ) (result: Int) (h_precond : sumSquaresCeil_precond (lst)) :=
  -- !benchmark @start postcond
  result = (lst.map (fun x => (⌈x⌉ : Int) * (⌈x⌉ : Int))).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumSquaresCeil_spec_satisfied (lst : List ℚ) (h_precond : sumSquaresCeil_precond (lst)) :
    sumSquaresCeil_postcond (lst) (sumSquaresCeil (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
