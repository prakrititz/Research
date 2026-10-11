-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isBalanced (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ')' ≤ (l.take k).count '(') ∧ l.count '(' = l.count ')'
-- !benchmark @end precond_aux

@[reducible, simp]
def separateParenGroups_precond (paren_string : String) : Prop :=
  -- !benchmark @start precond
  isBalanced (paren_string.toList.filter (fun c => c != ' ')) ∧ paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def separateParenGroups (paren_string : String) (h_precond : separateParenGroups_precond (paren_string)) : List String :=
  -- !benchmark @start code
  Id.run do
    let mut cnt : Int := 0
    let mut group : List Char := []
    let mut results : List String := []
    for ch in paren_string.toList do
      if ch == '(' then cnt := cnt + 1
      if ch == ')' then cnt := cnt - 1
      if ch != ' ' then group := group ++ [ch]
      if cnt == 0 then
        if group != [] then results := results ++ [String.mk group]
        group := []
    return results
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def separateParenGroups_postcond (paren_string : String) (result: List String) (h_precond : separateParenGroups_precond (paren_string)) :=
  -- !benchmark @start postcond
  (result.map String.toList).flatten = paren_string.toList.filter (fun c => c != ' ') ∧
    ∀ g ∈ result, g.length > 0 ∧ isBalanced g.toList ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.toList.take k)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem separateParenGroups_spec_satisfied (paren_string : String) (h_precond : separateParenGroups_precond (paren_string)) :
    separateParenGroups_postcond (paren_string) (separateParenGroups (paren_string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
