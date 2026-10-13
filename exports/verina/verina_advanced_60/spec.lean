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
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True

@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  let evens := result.fst
  let odds := result.snd
  -- All elements from nums are in evens ++ odds, no extras
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)
