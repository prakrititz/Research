-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def fib4Spec : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | (n + 4) => fib4Spec (n + 3) + fib4Spec (n + 2) + fib4Spec (n + 1) + fib4Spec n
-- !benchmark @end precond_aux

@[reducible, simp]
def fib4_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fib4 (n : Nat) (h_precond : fib4_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut a := 0
    let mut b := 0
    let mut c := 2
    let mut d := 0
    if n == 0 then return 0
    if n == 1 then return 0
    if n == 2 then return 2
    for _ in [4:n + 1] do
      (a, b, c, d) := (b, c, d, a + b + c + d)
    return d
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fib4_postcond (n : Nat) (result: Nat) (h_precond : fib4_precond (n)) :=
  -- !benchmark @start postcond
  result = fib4Spec n
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fib4_spec_satisfied (n : Nat) (h_precond : fib4_precond (n)) :
    fib4_postcond (n) (fib4 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
