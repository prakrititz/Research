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
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  k ≤ nums.eraseDups.length

@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal (simplified: no tie-breaking constraint on ordering)
  (result.all (fun x =>
    nums.all (fun y =>
      y ∈ result ∨ nums.count x ≥ nums.count y
    ))) ∧

  -- Elements in result are ordered by non-increasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x ≥ nums.count y
  ) result.zipIdx
