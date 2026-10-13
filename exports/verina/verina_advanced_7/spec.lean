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
def binaryToDecimal_precond (digits : List Nat) : Prop :=
  digits.all (fun d => d = 0 ∨ d = 1)

@[reducible]
def binaryToDecimal_postcond (digits : List Nat) (result: Nat) (h_precond : binaryToDecimal_precond (digits)) : Prop :=
  result - List.foldl (λ acc bit => acc * 2 + bit) 0 digits = 0 ∧
  List.foldl (λ acc bit => acc * 2 + bit) 0 digits - result = 0
