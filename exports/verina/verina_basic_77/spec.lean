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
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  index1 < arr.size ∧
  index2 < (arr[index1]!).size

@[reducible, simp]
def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :=
  result.size = arr.size ∧
  (result[index1]!).size = (arr[index1]!).size ∧
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!) ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)
