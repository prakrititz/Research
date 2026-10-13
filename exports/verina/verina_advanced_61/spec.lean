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
def productExceptSelf_precond (nums : List Int) : Prop :=
  True

-- Specification Helper: Product of a list of Ints
-- Defined locally if not available/imported
def List.myprod : List Int → Int
  | [] => 1
  | x :: xs => x * xs.myprod

@[reducible]
def productExceptSelf_postcond (nums : List Int) (result: List Int) (h_precond : productExceptSelf_precond (nums)) : Prop :=
  nums.length = result.length ∧
  (List.range nums.length |>.all (fun i =>
    result[i]! = some (((List.take i nums).myprod) * ((List.drop (i+1) nums).myprod))))
