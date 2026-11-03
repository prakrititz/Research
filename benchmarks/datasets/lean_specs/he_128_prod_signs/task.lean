-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def prodSigns_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def prodSigns (arr : List Int) (h_precond : prodSigns_precond (arr)) : Option Int :=
  -- !benchmark @start code
  if arr = [] then none else some ((arr.foldl (fun (s : Int) (x : Int) => s + (x.natAbs : Int)) 0) * (arr.foldl (fun (p : Int) (x : Int) => p * x.sign) 1))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def prodSigns_postcond (arr : List Int) (result: Option Int) (h_precond : prodSigns_precond (arr)) :=
  -- !benchmark @start postcond
  match result with
  | none => arr = []
  | some r => arr ≠ [] ∧ r = (arr.map (fun (x : Int) => (x.natAbs : Int))).sum * (arr.map Int.sign).prod
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem prodSigns_spec_satisfied (arr : List Int) (h_precond : prodSigns_precond (arr)) :
    prodSigns_postcond (arr) (prodSigns (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
