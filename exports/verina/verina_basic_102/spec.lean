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
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size > 1 ∧ ¬ List.Pairwise (fun a b => a + b ≠ target) nums.toList

@[reducible, simp]
def twoSum_postcond (nums : Array Int) (target : Int) (result: (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) :=
  let (i, j) := result
  -- Basic validity: i < j, in bounds, and sum equals target
  i < j ∧ j < nums.size ∧ nums[i]! + nums[j]! = target ∧
  -- Lexicographically first: no valid pair (i', j') with i' < i exists
  (nums.toList.take i).zipIdx.all (fun ⟨a, i'⟩ =>
    (nums.toList.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
  -- For our i, j is the smallest valid partner
  ((nums.toList.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)
