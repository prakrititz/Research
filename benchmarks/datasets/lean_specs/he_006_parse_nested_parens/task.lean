-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def maxDepth (l : List Char) : Nat :=
  (((List.range (l.length + 1)).map (fun k => ((l.take k).count '(' : Int) - ((l.take k).count ')' : Int))).foldl max 0).toNat
-- !benchmark @end precond_aux

@[reducible, simp]
def parseNestedParens_precond (paren_string : String) : Prop :=
  -- !benchmark @start precond
  paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def parseNestedParens (paren_string : String) (h_precond : parseNestedParens_precond (paren_string)) : List Nat :=
  -- !benchmark @start code
  ((paren_string.splitOn " ").filter (fun g => g != "")).map (fun g => maxDepth g.toList)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def parseNestedParens_postcond (paren_string : String) (result: List Nat) (h_precond : parseNestedParens_precond (paren_string)) :=
  -- !benchmark @start postcond
  let groups := (paren_string.splitOn " ").filter (fun g => g != "")
  result.length = groups.length ∧ ∀ i, i < groups.length → result[i]! = maxDepth groups[i]!.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem parseNestedParens_spec_satisfied (paren_string : String) (h_precond : parseNestedParens_precond (paren_string)) :
    parseNestedParens_postcond (paren_string) (parseNestedParens (paren_string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
