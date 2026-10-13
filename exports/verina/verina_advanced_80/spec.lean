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
def twoSum_precond (nums : Array Int) (target : Int) : Prop :=
  -- The array must have at least 2 elements
  nums.size ≥ 2 ∧

  -- There exists exactly one pair of indices whose values sum to the target
  (List.range nums.size).any (fun i =>
    (List.range i).any (fun j => nums[i]! + nums[j]! = target)) ∧

  -- No other pair sums to the target (ensuring uniqueness of solution)
  ((List.range nums.size).flatMap (fun i =>
    (List.range i).filter (fun j => nums[i]! + nums[j]! = target))).length = 1

@[reducible]
def twoSum_postcond (nums : Array Int) (target : Int) (result: Array Nat) (h_precond : twoSum_precond (nums) (target)) : Prop :=
  -- Result contains exactly 2 indices
  result.size = 2 ∧

  -- The indices are valid (within bounds of the nums array)
  result[0]! < nums.size ∧ result[1]! < nums.size ∧

  -- The indices are in ascending order (sorted)
  result[0]! < result[1]! ∧

  -- The values at these indices sum to the target
  nums[result[0]!]! + nums[result[1]!]! = target
