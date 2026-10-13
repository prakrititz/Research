import Mathlib

@[reducible, simp]
def vowelsCount_precond (s : String) : Prop :=
  True

@[reducible, simp]
def vowelsCount_postcond (s : String) (result: Nat) (h_precond : vowelsCount_precond (s)) :=
  result = (s.toList.filter (fun c => ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)).length +
      (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0)
