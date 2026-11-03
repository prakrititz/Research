-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def fibfibSpec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => fibfibSpec (n + 2) + fibfibSpec (n + 1) + fibfibSpec n
-- !benchmark @end precond_aux

@[reducible, simp]
def fibfib_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fibfib (n : Nat) (h_precond : fibfib_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    if n == 0 then return 0
    if n == 1 then return 0
    let mut a := 0
    let mut b := 0
    let mut c := 1
    for _ in [3:n + 1] do
      (a, b, c) := (b, c, a + b + c)
    return c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fibfib_postcond (n : Nat) (result: Nat) (h_precond : fibfib_precond (n)) :=
  -- !benchmark @start postcond
  result = fibfibSpec n
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fibfib_spec_satisfied (n : Nat) (h_precond : fibfib_precond (n)) :
    fibfib_postcond (n) (fibfib (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
