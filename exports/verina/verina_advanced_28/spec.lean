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

@[reducible, simp]
def longestConsecutive_precond (nums : List Int) : Prop :=
  List.Nodup nums

def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)

@[reducible, simp]
def longestConsecutive_postcond (nums : List Int) (result: Nat) (h_precond : longestConsecutive_precond (nums)) : Prop :=
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)

  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))
