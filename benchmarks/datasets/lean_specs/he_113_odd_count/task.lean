-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def oddDigits (s : String) : Nat := (s.toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length
def oddMsg (n : Nat) : String := "the number of odd elements in the string i of the input.".replace "i" (toString n)
-- !benchmark @end precond_aux

@[reducible, simp]
def oddCount_precond (lst : List String) : Prop :=
  -- !benchmark @start precond
  ∀ s ∈ lst, s.toList.all Char.isDigit = true
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def oddCount (lst : List String) (h_precond : oddCount_precond (lst)) : List String :=
  -- !benchmark @start code
  lst.map (fun s => oddMsg (oddDigits s))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def oddCount_postcond (lst : List String) (result: List String) (h_precond : oddCount_precond (lst)) :=
  -- !benchmark @start postcond
  result.length = lst.length ∧ ∀ k, k < lst.length → result[k]! = oddMsg (oddDigits lst[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem oddCount_spec_satisfied (lst : List String) (h_precond : oddCount_precond (lst)) :
    oddCount_postcond (lst) (oddCount (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
