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
def trapRainWater_precond (height : List Nat) : Prop :=
  True

@[reducible, simp]
def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result
