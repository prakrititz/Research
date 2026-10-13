import Mathlib

@[reducible, simp] def isBalanced (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ')' ≤ (l.take k).count '(') ∧ l.count '(' = l.count ')'

@[reducible, simp]
def separateParenGroups_precond (paren_string : String) : Prop :=
  isBalanced (paren_string.toList.filter (fun c => c != ' ')) ∧ paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')

@[reducible, simp]
def separateParenGroups_postcond (paren_string : String) (result: List String) (h_precond : separateParenGroups_precond (paren_string)) :=
  (result.map String.toList).flatten = paren_string.toList.filter (fun c => c != ' ') ∧
    ∀ g ∈ result, g.length > 0 ∧ isBalanced g.toList ∧ ∀ k, k < g.length → 0 < k → ¬ isBalanced (g.toList.take k)
