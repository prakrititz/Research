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
def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)

@[reducible]
def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : Prop :=
  result.length = nums1.length ∧

  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!

    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )

      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))
