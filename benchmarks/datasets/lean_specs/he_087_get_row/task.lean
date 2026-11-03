-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def getRow_precond (lst : List (List Int)) (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def getRow (lst : List (List Int)) (x : Int) (h_precond : getRow_precond (lst) (x)) : List (Nat × Nat) :=
  -- !benchmark @start code
  ((List.range lst.length).map (fun i => ((List.range lst[i]!.length).reverse.filter (fun j => (lst[i]!)[j]! == x)).map (fun j => (i, j)))).flatten
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def getRow_postcond (lst : List (List Int)) (x : Int) (result: List (Nat × Nat)) (h_precond : getRow_precond (lst) (x)) :=
  -- !benchmark @start postcond
  (∀ p ∈ result, p.1 < lst.length ∧ p.2 < lst[p.1]!.length ∧ (lst[p.1]!)[p.2]! = x) ∧
    (∀ i, i < lst.length → ∀ j, j < lst[i]!.length → (lst[i]!)[j]! = x → (i, j) ∈ result) ∧ result.Nodup ∧
    ∀ k, k < result.length - 1 → result[k]!.1 < result[k + 1]!.1 ∨ (result[k]!.1 = result[k + 1]!.1 ∧ result[k + 1]!.2 < result[k]!.2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem getRow_spec_satisfied (lst : List (List Int)) (x : Int) (h_precond : getRow_precond (lst) (x)) :
    getRow_postcond (lst) (x) (getRow (lst) (x) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
