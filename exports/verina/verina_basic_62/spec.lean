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
def Find_precond (a : Array Int) (key : Int) : Prop :=
  True

@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)
