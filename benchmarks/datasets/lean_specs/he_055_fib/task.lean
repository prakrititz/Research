-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def fib_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fib (n : Nat) (h_precond : fib_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut a := 0
    let mut b := 1
    for _ in [0:n] do
      (a, b) := (b, a + b)
    return a
  -- !benchmark @end code


-- !benchmark @start postcond_aux
@[simp] def fibSpec : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibSpec n + fibSpec (n + 1)
-- !benchmark @end postcond_aux


@[reducible, simp]
def fib_postcond (n : Nat) (result: Nat) (h_precond : fib_precond (n)) :=
  -- !benchmark @start postcond
  result = fibSpec n
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fib_spec_satisfied (n : Nat) (h_precond : fib_precond (n)) :
    fib_postcond (n) (fib (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
