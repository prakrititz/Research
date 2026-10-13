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

@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  True

@[reducible, simp]
def LongestCommonPrefix_postcond (str1 : List Char) (str2 : List Char) (result: List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :=
  (result.length ≤ str1.length) ∧ (result = str1.take result.length) ∧
  (result.length ≤ str2.length) ∧ (result = str2.take result.length) ∧
  (result.length = str1.length ∨ result.length = str2.length ∨
    (str1[result.length]? ≠ str2[result.length]?))
