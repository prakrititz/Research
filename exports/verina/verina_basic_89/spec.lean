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
def SetToSeq_precond (s : List Int) : Prop :=
  True

@[reducible, simp]
def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  -- Contains exactly the elements of the set
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  -- All elements are unique in the result
  result.all (fun a => result.count a = 1) ∧
  -- The order of elements in the result is preserved
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result
