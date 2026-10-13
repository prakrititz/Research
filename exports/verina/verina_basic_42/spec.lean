import Mathlib
namespace Array
def mkArray {α : Type} (n : Nat) (v : α) : Array α := Array.replicate n v
end Array
namespace Std.HashSet
def empty {α : Type} [BEq α] [Hashable α] : Std.HashSet α := {}
end Std.HashSet
syntax "wit_search" : tactic
macro_rules
  | `(tactic| wit_search) => `(tactic| first
      | decide
      | (refine ⟨?_, ?_⟩ <;> wit_search)
      | (refine ⟨0, ?_⟩; wit_search) | (refine ⟨1, ?_⟩; wit_search) | (refine ⟨2, ?_⟩; wit_search)
      | (refine ⟨3, ?_⟩; wit_search) | (refine ⟨4, ?_⟩; wit_search) | (refine ⟨5, ?_⟩; wit_search))

def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  True

@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0
