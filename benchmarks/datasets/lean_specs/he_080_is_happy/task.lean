-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isHappy_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isHappy (s : String) (h_precond : isHappy_precond (s)) : Bool :=
  -- !benchmark @start code
  decide (s.length ≥ 3) && (List.range (s.length - 2)).all (fun i =>
    s.toList[i]! != s.toList[i + 1]! && s.toList[i]! != s.toList[i + 2]! && s.toList[i + 1]! != s.toList[i + 2]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isHappy_postcond (s : String) (result: Bool) (h_precond : isHappy_precond (s)) :=
  -- !benchmark @start postcond
  result = true ↔ (s.length ≥ 3 ∧ ∀ i, i < s.length - 2 → s.toList[i]! ≠ s.toList[i + 1]! ∧ s.toList[i]! ≠ s.toList[i + 2]! ∧
      s.toList[i + 1]! ≠ s.toList[i + 2]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isHappy_spec_satisfied (s : String) (h_precond : isHappy_precond (s)) :
    isHappy_postcond (s) (isHappy (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
