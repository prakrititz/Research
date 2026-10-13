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
def findFirstRepeatedChar_precond (s : String) : Prop :=
  True

@[reducible, simp]
def findFirstRepeatedChar_postcond (s : String) (result: Option Char) (h_precond : findFirstRepeatedChar_precond (s)) :=
  let cs := s.toList
  match result with
  | some c =>
    let secondIdx := cs.zipIdx.findIdx (fun (x, i) => x = c && i ≠ cs.idxOf c)
    -- Exists repeated char
    cs.count c ≥ 2 ∧
    -- There is no other repeated char before the found one
    List.Pairwise (· ≠ ·) (cs.take secondIdx)
  | none =>
    -- There is no repeated char
    List.Pairwise (· ≠ ·) cs
