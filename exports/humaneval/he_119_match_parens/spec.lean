import Mathlib

@[reducible, simp] def isBalanced (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ')' ≤ (l.take k).count '(') ∧ l.count '(' = l.count ')'

@[reducible, simp]
def matchParens_precond (lst : List String) : Prop :=
  lst.length = 2 ∧ lst.all (fun t => t.toList.all (fun c => c == '(' || c == ')')) = true

@[reducible, simp]
def matchParens_postcond (lst : List String) (result: String) (h_precond : matchParens_precond (lst)) :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ (isBalanced (lst[0]!.toList ++ lst[1]!.toList) ∨ isBalanced (lst[1]!.toList ++ lst[0]!.toList)))
