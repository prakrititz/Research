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

def countOnes (lst : List Char) : Nat :=
  lst.foldl (fun acc c => if c = '1' then acc + 1 else acc) 0

@[reducible]
def shortestBeautifulSubstring_precond (s : String) (k : Nat) : Prop :=
  s.toList.all (fun c => c = '0' ∨ c = '1')

@[reducible]
def shortestBeautifulSubstring_postcond (s : String) (k : Nat) (result: String) (h_precond : shortestBeautifulSubstring_precond (s) (k)) : Prop :=
  let chars := s.data
  let substrings := (List.range chars.length).flatMap (fun i =>
    (List.range (chars.length - i + 1)).map (fun len =>
      chars.drop i |>.take len))
  let isBeautiful := fun sub => countOnes sub = k
  let beautiful := substrings.filter (fun sub => isBeautiful sub)
  let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ "")
  (result = "" ∧ targets = []) ∨
  (result ∈ targets ∧
   ∀ r ∈ targets, r.length > result.length ∨ (r.length = result.length ∧ result ≤ r))
