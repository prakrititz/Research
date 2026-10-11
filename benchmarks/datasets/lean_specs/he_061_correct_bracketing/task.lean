-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def correctBracketing_precond (brackets : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def correctBracketing (brackets : String) (h_precond : correctBracketing_precond (brackets)) : Bool :=
  -- !benchmark @start code
  Id.run do
    let mut depth : Int := 0
    for c in brackets.toList do
      if c == '(' then depth := depth + 1
      else if c == ')' then depth := depth - 1
      if depth < 0 then return false
    return depth == 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def correctBracketing_postcond (brackets : String) (result: Bool) (h_precond : correctBracketing_precond (brackets)) :=
  -- !benchmark @start postcond
  result = true ↔ ((∀ k, k ≤ brackets.length → (brackets.toList.take k).count '(' ≥ (brackets.toList.take k).count ')') ∧ brackets.toList.count '(' = brackets.toList.count ')')
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem correctBracketing_spec_satisfied (brackets : String) (h_precond : correctBracketing_precond (brackets)) :
    correctBracketing_postcond (brackets) (correctBracketing (brackets) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
