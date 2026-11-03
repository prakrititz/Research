-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def modp_precond (n : Nat) (p : Nat) : Prop :=
  -- !benchmark @start precond
  p > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def modp (n : Nat) (p : Nat) (h_precond : modp_precond (n) (p)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut res := 1
    let mut x := 2
    let mut m := n
    while m != 0 do
      if m % 2 == 1 then res := res * x % p
      x := x * x % p
      m := m / 2
    return res % p
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def modp_postcond (n : Nat) (p : Nat) (result: Nat) (h_precond : modp_precond (n) (p)) :=
  -- !benchmark @start postcond
  result = 2 ^ n % p
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem modp_spec_satisfied (n : Nat) (p : Nat) (h_precond : modp_precond (n) (p)) :
    modp_postcond (n) (p) (modp (n) (p) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
