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
def lengthOfLIS_precond (nums : List Int) : Prop :=
  True

@[reducible, simp]
def lengthOfLIS_postcond (nums : List Int) (result: Int) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  -- Helper function to check strictly increasing
  let rec isStrictlyIncreasing (l : List Int) : Bool :=
    match l with
    | [] | [_] => true
    | x :: y :: rest => x < y && isStrictlyIncreasing (y :: rest)

  -- Generate all subsequences
  let rec subsequences (xs : List Int) : List (List Int) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
      let rest := subsequences xs'
      rest ++ rest.map (fun r => x :: r)

  let allIncreasing := subsequences nums |>.filter (fun l => isStrictlyIncreasing l)

  allIncreasing.any (fun l => l.length = result) ∧
  allIncreasing.all (fun l => l.length ≤ result)
