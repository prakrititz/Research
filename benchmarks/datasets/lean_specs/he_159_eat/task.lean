-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def eat_precond (number : Nat) (need : Nat) (remaining : Nat) : Prop :=
  -- !benchmark @start precond
  number ≤ 1000 ∧ need ≤ 1000 ∧ remaining ≤ 1000
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def eat (number : Nat) (need : Nat) (remaining : Nat) (h_precond : eat_precond (number) (need) (remaining)) : List Nat :=
  -- !benchmark @start code
  if need ≤ remaining then [number + need, remaining - need] else [number + remaining, 0]
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def eat_postcond (number : Nat) (need : Nat) (remaining : Nat) (result: List Nat) (h_precond : eat_precond (number) (need) (remaining)) :=
  -- !benchmark @start postcond
  result.length = 2 ∧ result[0]! = number + min need remaining ∧ result[1]! = remaining - min need remaining
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem eat_spec_satisfied (number : Nat) (need : Nat) (remaining : Nat) (h_precond : eat_precond (number) (need) (remaining)) :
    eat_postcond (number) (need) (remaining) (eat (number) (need) (remaining) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
