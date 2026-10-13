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

@[reducible]
def mergeSortedLists_precond (arr1 : List Int) (arr2 : List Int) : Prop :=
  List.Pairwise (· ≤ ·) arr1 ∧ List.Pairwise (· ≤ ·) arr2

@[reducible]
def mergeSortedLists_postcond (arr1 : List Int) (arr2 : List Int) (result: List Int) (h_precond : mergeSortedLists_precond (arr1) (arr2)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm (arr1 ++ arr2) result
