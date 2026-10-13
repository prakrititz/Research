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
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)

@[reducible, simp]
def minOperations_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : minOperations_precond (nums) (k)) : Prop :=
  -- define the list of elements processed after `result` operations
  let processed := (nums.reverse).take result
  -- define the target numbers to collect (1 to k)
  let target_nums := (List.range k).map (· + 1)

  -- condition 1: All target numbers must be present in the processed elements
  let collected_all := target_nums.all (fun n => List.elem n processed)

  -- condition 2: `result` must be the minimum number of operations.
  -- This means either result is 0 (which implies k must be 0 as target_nums would be empty)
  -- or result > 0, and taking one less operation (result - 1) is not sufficient
  let is_minimal :=
    if result > 0 then
      -- if one fewer element is taken, not all target numbers should be present
      let processed_minus_one := (nums.reverse).take (result - 1)
      ¬ (target_nums.all (fun n => List.elem n processed_minus_one))
    else
      -- if result is 0, it can only be minimal if k is 0 (no targets required)
      -- So if k=0, `collected_all` is true. If result=0, this condition `k==0` ensures minimality.
      k == 0

  -- overall specification:
  collected_all ∧ is_minimal
