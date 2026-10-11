-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def strength (s : String) : Int := ((s.toList.filter Char.isUpper).length : Int) - ((s.toList.filter Char.isLower).length : Int)
-- !benchmark @end precond_aux

@[reducible, simp]
def strongestExtension_precond (class_name : String) (extensions : List String) : Prop :=
  -- !benchmark @start precond
  extensions ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def strongestExtension (class_name : String) (extensions : List String) (h_precond : strongestExtension_precond (class_name) (extensions)) : String :=
  -- !benchmark @start code
  class_name ++ "." ++ extensions.foldl (fun (b : String) e => if strength e > strength b then e else b) extensions.head!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def strongestExtension_postcond (class_name : String) (extensions : List String) (result: String) (h_precond : strongestExtension_precond (class_name) (extensions)) :=
  -- !benchmark @start postcond
  ∃ i, i < extensions.length ∧ result = class_name ++ "." ++ extensions[i]! ∧
    (∀ j, j < extensions.length → strength extensions[j]! ≤ strength extensions[i]!) ∧ ∀ j, j < i → strength extensions[j]! < strength extensions[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem strongestExtension_spec_satisfied (class_name : String) (extensions : List String) (h_precond : strongestExtension_precond (class_name) (extensions)) :
    strongestExtension_postcond (class_name) (extensions) (strongestExtension (class_name) (extensions) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
