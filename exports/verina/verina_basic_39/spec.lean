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
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  True

@[reducible, simp]
def rotateRight_postcond (l : List Int) (n : Nat) (result: List Int) (h_precond : rotateRight_precond (l) (n)) :=
  result.length = l.length ∧
  (∀ i : Nat, i < l.length →
    let len := l.length
    let rotated_index := Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
    result[i]? = l[rotated_index]?)
