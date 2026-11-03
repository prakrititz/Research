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
def matchParens_precond (lst : List String) : Prop :=
  -- !benchmark @start precond
  lst.length = 2 ∧ lst.all (fun t => t.toList.all (fun c => c == '(' || c == ')')) = true
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def matchParens (lst : List String) (h_precond : matchParens_precond (lst)) : String :=
  -- !benchmark @start code
  let a := lst[0]!.toList
  let b := lst[1]!.toList
  let ok := fun (l : List Char) => decide (isBalanced l)
  if ok (a ++ b) || ok (b ++ a) then "Yes" else "No"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def matchParens_postcond (lst : List String) (result: String) (h_precond : matchParens_precond (lst)) :=
  -- !benchmark @start postcond
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ (isBalanced (lst[0]!.toList ++ lst[1]!.toList) ∨ isBalanced (lst[1]!.toList ++ lst[0]!.toList)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem matchParens_spec_satisfied (lst : List String) (h_precond : matchParens_precond (lst)) :
    matchParens_postcond (lst) (matchParens (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
