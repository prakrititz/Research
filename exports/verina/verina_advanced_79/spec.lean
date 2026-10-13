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
def twoSum_precond (nums : List Int) (target : Int) : Prop :=
  True

@[reducible]
def twoSum_postcond (nums : List Int) (target : Int) (result: Option (Nat × Nat)) (h_precond : twoSum_precond (nums) (target)) : Prop :=
    match result with
    | none => List.Pairwise (· + · ≠ target) nums
    | some (i, j) =>
        i < j ∧
        j < nums.length ∧
        nums[i]! + nums[j]! = target ∧
        -- Lexicographically first: no valid pair (i', j') with i' < i exists
        (nums.take i).zipIdx.all (fun ⟨a, i'⟩ =>
          (nums.drop (i' + 1)).all (fun b => a + b ≠ target)) ∧
        -- For this i, j is the smallest valid partner
        ((nums.drop (i + 1)).take (j - i - 1)).all (fun b => nums[i]! + b ≠ target)
