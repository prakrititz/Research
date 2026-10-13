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
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList

@[reducible, simp]
def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))
