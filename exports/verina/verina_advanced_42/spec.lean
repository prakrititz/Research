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
def maxProfit_precond (prices : List Nat) : Prop :=
  True

@[reducible, simp]
def maxProfit_postcond (prices : List Nat) (result: Nat) (h_precond : maxProfit_precond (prices)) : Prop :=
  -- All valid transactions have profit ≤ result
  List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧
  -- result = 0 when no profitable transaction exists (empty, single element, or decreasing prices)
  (result = 0 ↔
    (prices.length ≤ 1 ∨
     prices.zipIdx.all (fun ⟨pi, i⟩ =>
       prices.zipIdx.all (fun ⟨pj, j⟩ => i ≥ j ∨ pj ≤ pi)))) ∧
  -- If result > 0, there exists a transaction achieving it
  (result > 0 → prices.zipIdx.any (fun ⟨pi, i⟩ =>
    prices.zipIdx.any (fun ⟨pj, j⟩ => i < j ∧ pj - pi = result)))
