-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def numeralNames : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]
def numeralValue (t : String) : Nat := numeralNames.idxOf t
-- !benchmark @end precond_aux

@[reducible, simp]
def sortNumbers_precond (numbers : String) : Prop :=
  -- !benchmark @start precond
  numbers = "" ∨ ∀ t ∈ numbers.splitOn " ", t ∈ numeralNames
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortNumbers (numbers : String) (h_precond : sortNumbers_precond (numbers)) : String :=
  -- !benchmark @start code
  " ".intercalate (((if numbers = "" then [] else numbers.splitOn " ")).mergeSort (fun a b => numeralValue a ≤ numeralValue b))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortNumbers_postcond (numbers : String) (result: String) (h_precond : sortNumbers_precond (numbers)) :=
  -- !benchmark @start postcond
  let toks := if numbers = "" then [] else numbers.splitOn " "
  let sorted := if result = "" then [] else result.splitOn " "
  sorted.isPerm toks ∧ ∀ i, i < sorted.length - 1 → numeralValue sorted[i]! ≤ numeralValue sorted[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortNumbers_spec_satisfied (numbers : String) (h_precond : sortNumbers_precond (numbers)) :
    sortNumbers_postcond (numbers) (sortNumbers (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
