import Mathlib

@[reducible, simp] def isBalancedSq (l : List Char) : Prop :=
  (∀ k, k ≤ l.length → (l.take k).count ']' ≤ (l.take k).count '[') ∧ l.count '[' = l.count ']'

@[reducible, simp]
def isNested_precond (string : String) : Prop :=
  string.toList.all (fun c => c == '[' || c == ']') = true

@[reducible, simp]
def isNested_postcond (string : String) (result: Bool) (h_precond : isNested_precond (string)) :=
  result = true ↔ ∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧
      isBalancedSq ((string.toList.drop i).take len) ∧ ∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k)
