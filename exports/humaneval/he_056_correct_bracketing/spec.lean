import Mathlib

@[reducible, simp]
def correctBracketing56_precond (brackets : String) : Prop :=
  brackets.toList.all (fun c => c == '<' || c == '>') = true

@[reducible, simp]
def correctBracketing56_postcond (brackets : String) (result: Bool) (h_precond : correctBracketing56_precond (brackets)) :=
  result = true ↔ ((∀ k, k ≤ brackets.length → (brackets.toList.take k).count '>' ≤ (brackets.toList.take k).count '<') ∧
      brackets.toList.count '<' = brackets.toList.count '>')
