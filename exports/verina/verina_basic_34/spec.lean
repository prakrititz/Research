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

def isEven (n : Int) : Bool :=
  n % 2 = 0

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  True

@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  result.all (fun x => isEven x ∧ x ∈ arr.toList ∧ result.toList.count x = arr.toList.count x) ∧
  arr.all (fun x => isEven x → x ∈ result.toList) ∧
  arr.all (fun x => arr.all (fun y =>
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y
  ))
