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
def insert_precond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) : Prop :=
  l ≤ oline.size ∧
  p ≤ nl.size ∧
  atPos ≤ l

@[reducible, simp]
def insert_postcond (oline : Array Char) (l : Nat) (nl : Array Char) (p : Nat) (atPos : Nat) (result: Array Char) (h_precond : insert_precond (oline) (l) (nl) (p) (atPos)) :=
  result.size = l + p ∧
  (List.range p).all (fun i => result[atPos + i]! = nl[i]!) ∧
  (List.range atPos).all (fun i => result[i]! = oline[i]!) ∧
  (List.range (l - atPos)).all (fun i => result[atPos + p + i]! = oline[atPos + i]!)
