import Mathlib

@[reducible, simp]
def sortedListSum_precond (lst : List String) : Prop :=
  True

@[reducible, simp]
def sortedListSum_postcond (lst : List String) (result: List String) (h_precond : sortedListSum_precond (lst)) :=
  List.Perm result (lst.filter (fun s => s.length % 2 = 0)) ∧
    ∀ i, i < result.length - 1 → (result[i]!.length < result[i + 1]!.length ∨ (result[i]!.length = result[i + 1]!.length ∧ ¬ (result[i + 1]! < result[i]!)))
