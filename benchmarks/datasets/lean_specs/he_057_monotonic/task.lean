-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def monotonic_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def monotonic (l : List Int) (h_precond : monotonic_precond (l)) : Bool :=
  -- !benchmark @start code
  (List.range (l.length - 1)).all (fun i => l[i]! ≤ l[i + 1]!) || (List.range (l.length - 1)).all (fun i => l[i]! ≥ l[i + 1]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def monotonic_postcond (l : List Int) (result: Bool) (h_precond : monotonic_precond (l)) :=
  -- !benchmark @start postcond
  result = true ↔ ((∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) ∨ (∀ i, i < l.length - 1 → l[i]! ≥ l[i + 1]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem monotonic_spec_satisfied (l : List Int) (h_precond : monotonic_precond (l)) :
    monotonic_postcond (l) (monotonic (l) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
