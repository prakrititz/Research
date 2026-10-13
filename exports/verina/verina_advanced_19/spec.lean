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

-- Check if a character is an uppercase alphabet letter
def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

-- Check if a character is a lowercase alphabet letter
def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

-- Determine if a character is alphabetic
def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

-- Convert a single character to lowercase
def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []

@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  True

@[reducible]
def isCleanPalindrome_postcond (s : String) (result: Bool) (h_precond : isCleanPalindrome_precond (s)) : Prop :=
  let norm := normalizeString s
  (result = true → norm = norm.reverse) ∧
  (result = false → norm ≠ norm.reverse)
