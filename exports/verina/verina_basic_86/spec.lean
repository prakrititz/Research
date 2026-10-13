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
def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  offset ≥ 0

@[reducible, simp]
def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)
