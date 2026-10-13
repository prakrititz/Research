import Mathlib

@[reducible, simp]
def isHappy_precond (s : String) : Prop :=
  True

@[reducible, simp]
def isHappy_postcond (s : String) (result: Bool) (h_precond : isHappy_precond (s)) :=
  result = true ↔ (s.length ≥ 3 ∧ ∀ i, i < s.length - 2 → s.toList[i]! ≠ s.toList[i + 1]! ∧ s.toList[i]! ≠ s.toList[i + 2]! ∧
      s.toList[i + 1]! ≠ s.toList[i + 2]!)
