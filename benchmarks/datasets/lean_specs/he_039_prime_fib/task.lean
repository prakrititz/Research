-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def primeFib_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def primeFib (n : Nat) (h_precond : primeFib_precond (n)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut count := 0
    let mut k := 0
    let mut res := 0
    while count < n do
      k := k + 1
      if decide (Nat.Prime (Nat.fib k)) then
        count := count + 1
        res := Nat.fib k
    return res
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def primeFib_postcond (n : Nat) (result: Nat) (h_precond : primeFib_precond (n)) :=
  -- !benchmark @start postcond
  ∃ k, k < 300 ∧ Nat.fib k = result ∧ Nat.Prime result ∧
      (((List.range k).map Nat.fib).filter (fun m => decide (Nat.Prime m))).length = n - 1
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem primeFib_spec_satisfied (n : Nat) (h_precond : primeFib_precond (n)) :
    primeFib_postcond (n) (primeFib (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
