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

open Std

@[reducible]
def mostFrequent_precond (xs : List Int) : Prop :=
  xs ≠ []

@[reducible]
def mostFrequent_postcond (xs : List Int) (result: Int) (h_precond : mostFrequent_precond (xs)) : Prop :=
  let count := fun x => xs.countP (fun y => y = x)
  result ∈ xs ∧
  xs.all (fun x => count x ≤ count result) ∧
  ((xs.filter (fun x => count x = count result)).head? = some result)
