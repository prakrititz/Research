-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def atMod (m : Nat) (x : List Int) : List Int := ((List.range x.length).filter (fun i => i % m = 0)).map (fun i => x[i]!)
-- !benchmark @end precond_aux

@[reducible, simp]
def sortThird_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortThird (l : List Int) (h_precond : sortThird_precond (l)) : List Int :=
  -- !benchmark @start code
  let sorted := (atMod 3 l).mergeSort (fun a b => a ≤ b)
  (List.range l.length).map (fun i => if i % 3 = 0 then sorted[i / 3]! else l[i]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortThird_postcond (l : List Int) (result: List Int) (h_precond : sortThird_precond (l)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧ (∀ i, i < l.length → i % 3 ≠ 0 → result[i]! = l[i]!) ∧
    (atMod 3 result).isPerm (atMod 3 l) ∧ ∀ i, i < (atMod 3 result).length - 1 → (atMod 3 result)[i]! ≤ (atMod 3 result)[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortThird_spec_satisfied (l : List Int) (h_precond : sortThird_precond (l)) :
    sortThird_postcond (l) (sortThird (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
