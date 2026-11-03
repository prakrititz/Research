-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def encodeGroups : List Char → List Char
  | a :: b :: c :: rest => b :: c :: a :: encodeGroups rest
  | l => l
-- !benchmark @end precond_aux

@[reducible, simp]
def decodeCyclic_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def decodeCyclic (s : String) (h_precond : decodeCyclic_precond (s)) : String :=
  -- !benchmark @start code
  let rec decode : List Char → List Char
    | a :: b :: c :: rest => c :: a :: b :: decode rest
    | l => l
  String.mk (decode s.toList)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def decodeCyclic_postcond (s : String) (result: String) (h_precond : decodeCyclic_precond (s)) :=
  -- !benchmark @start postcond
  encodeGroups result.toList = s.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem decodeCyclic_spec_satisfied (s : String) (h_precond : decodeCyclic_precond (s)) :
    decodeCyclic_postcond (s) (decodeCyclic (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
