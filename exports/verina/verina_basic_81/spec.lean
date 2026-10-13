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
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  True

@[reducible, simp]
def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))
