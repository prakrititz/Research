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
def firstDuplicate_precond (lst : List Int) : Prop :=
  True

def secondOccIdx (lst : List Int) (v : Int) : Nat :=
  let first := lst.idxOf v
  first + 1 + (lst.drop (first + 1)).idxOf v

@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Option Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  match result with
  | none => List.Nodup lst
  | some x =>
      lst.count x > 1 ∧
      lst.all (fun y => (lst.count y = 1) ∨ (secondOccIdx lst x ≤ secondOccIdx lst y))
