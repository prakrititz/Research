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
def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  intervals.all (fun (s, e) => s ≤ e)

@[reducible, simp]
def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : Prop :=
  -- Check that all original intervals are covered by some result interval
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  -- Check that no intervals in the result overlap
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  let resultBounded := result.all (fun (rs, re) =>
    intervals.any (fun (s, _) => s = rs) ∧
    intervals.any (fun (_, e) => e = re))

  -- Check that no result interval spans a gap between non-overlapping inputs
  let noSpuriousMerge := result.all (fun (rs, re) =>
    (intervals.filter (fun (s, e) => rs ≤ s ∧ e ≤ re)).all (fun (s, _) =>
      s = rs ∨ intervals.any (fun (s2, e2) => rs ≤ s2 ∧ e2 ≤ re ∧ s2 < s ∧ e2 ≥ s)))

  covered ∧ noOverlap result ∧ resultBounded ∧ noSpuriousMerge
