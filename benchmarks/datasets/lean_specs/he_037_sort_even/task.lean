-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def atMod (m : Nat) (x : List Int) : List Int := ((List.range x.length).filter (fun i => i % m = 0)).map (fun i => x[i]!)
-- !benchmark @end precond_aux

@[reducible, simp]
def sortEven_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sortEven (l : List Int) (h_precond : sortEven_precond (l)) : List Int :=
  -- !benchmark @start code
  let sorted := (atMod 2 l).mergeSort (fun a b => a ≤ b)
  (List.range l.length).map (fun i => if i % 2 = 0 then sorted[i / 2]! else l[i]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sortEven_postcond (l : List Int) (result: List Int) (h_precond : sortEven_precond (l)) :=
  -- !benchmark @start postcond
  result.length = l.length ∧ (∀ i, i < l.length → i % 2 ≠ 0 → result[i]! = l[i]!) ∧
    (atMod 2 result).isPerm (atMod 2 l) ∧ ∀ i, i < (atMod 2 result).length - 1 → (atMod 2 result)[i]! ≤ (atMod 2 result)[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sortEven_spec_satisfied (l : List Int) (h_precond : sortEven_precond (l)) :
    sortEven_postcond (l) (sortEven (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
