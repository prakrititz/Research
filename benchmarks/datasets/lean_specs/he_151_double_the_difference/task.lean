-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def doubleTheDifference_precond (lst : List (Int ⊕ ℚ)) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def doubleTheDifference (lst : List (Int ⊕ ℚ)) (h_precond : doubleTheDifference_precond (lst)) : Int :=
  -- !benchmark @start code
  lst.foldl (fun (acc : Int) v => match v with | Sum.inl x => if x > 0 && x % 2 == 1 then acc + x * x else acc | Sum.inr _ => acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def doubleTheDifference_postcond (lst : List (Int ⊕ ℚ)) (result: Int) (h_precond : doubleTheDifference_precond (lst)) :=
  -- !benchmark @start postcond
  result = (lst.map (Sum.elim (fun (x : Int) => if x > 0 ∧ x % 2 = 1 then x * x else 0) (fun (_ : ℚ) => 0))).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem doubleTheDifference_spec_satisfied (lst : List (Int ⊕ ℚ)) (h_precond : doubleTheDifference_precond (lst)) :
    doubleTheDifference_postcond (lst) (doubleTheDifference (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
