-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def median_precond (l : List ℚ) : Prop :=
  -- !benchmark @start precond
  l ≠ []
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def median (l : List ℚ) (h_precond : median_precond (l)) : ℚ :=
  -- !benchmark @start code
  let s := l.mergeSort (fun a b => a ≤ b)
  if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def median_postcond (l : List ℚ) (result: ℚ) (h_precond : median_precond (l)) :=
  -- !benchmark @start postcond
  let s := l.mergeSort (fun a b => a ≤ b)
  |result - (if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2)| ≤ (1 / 1000000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem median_spec_satisfied (l : List ℚ) (h_precond : median_precond (l)) :
    median_postcond (l) (median (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
