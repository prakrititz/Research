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
def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  True

@[reducible]
def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : Prop :=
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)
