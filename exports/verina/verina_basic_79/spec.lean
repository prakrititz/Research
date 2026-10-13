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
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x > 0 ∧ x < a.size  -- x must be at least 1 (as stated in description)

@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  (∀ i, x ≤ i → i < p → a[i]! ≤ m) ∧
  (a[p]! > m ∨ (p = a.size - 1 ∧ ∀ i, x ≤ i → i < a.size → a[i]! ≤ m))
