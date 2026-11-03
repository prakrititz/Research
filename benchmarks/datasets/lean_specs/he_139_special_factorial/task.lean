-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def specialFactorial_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def specialFactorial (n : Nat) (h_precond : specialFactorial_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut fact := 1
    let mut total := 1
    for i in [1:n + 1] do
      fact := fact * i
      total := total * fact
    return total
  -- !benchmark @end code


-- !benchmark @start postcond_aux
@[simp] def factSpec : Nat → Nat
  | 0 => 1
  | (n + 1) => (n + 1) * factSpec n
-- !benchmark @end postcond_aux


@[reducible, simp]
def specialFactorial_postcond (n : Nat) (result: Nat) (h_precond : specialFactorial_precond (n)) :=
  -- !benchmark @start postcond
  result = ((List.range n).map (fun i => factSpec (i + 1))).prod
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem specialFactorial_spec_satisfied (n : Nat) (h_precond : specialFactorial_precond (n)) :
    specialFactorial_postcond (n) (specialFactorial (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
