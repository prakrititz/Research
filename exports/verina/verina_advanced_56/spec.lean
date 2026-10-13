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
def moveZeroes_precond (xs : List Int) : Prop :=
  True

def countVal (val : Int) : List Int → Nat
  | [] => 0
  | x :: xs =>
    let rest := countVal val xs
    if x = val then rest + 1 else rest

-- Check whether one list is a subsequence of another (preserving relative order)
def isSubsequence (xs ys : List Int) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | x :: xt, y :: yt =>
    if x = y then isSubsequence xt yt else isSubsequence xs yt

@[reducible]
def moveZeroes_postcond (xs : List Int) (result: List Int) (h_precond : moveZeroes_precond (xs)) : Prop :=
  -- 1. All non-zero elements must maintain their relative order
  isSubsequence (xs.filter (fun x => x ≠ 0)) result = true ∧

  -- 2. All zeroes must be located at the end of the output list
  (result.dropWhile (fun x => x ≠ 0)).all (fun x => x = 0) ∧

  -- 3. The output must contain the same number of elements,
  --    and the number of zeroes must remain unchanged
  countVal 0 xs = countVal 0 result ∧
  xs.length = result.length
