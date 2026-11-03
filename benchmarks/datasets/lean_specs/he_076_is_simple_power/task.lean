-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSimplePower_precond (x : Int) (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isSimplePower (x : Int) (n : Int) (h_precond : isSimplePower_precond (x) (n)) : Bool :=
  -- !benchmark @start code
  if x == 1 then true
  else if n == 0 then x == 0
  else if n == 1 then false
  else if n == -1 then x.natAbs == 1
  else Id.run do
    let mut p := n
    while p.natAbs ≤ x.natAbs do
      if p == x then return true
      p := p * n
    return false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isSimplePower_postcond (x : Int) (n : Int) (result: Bool) (h_precond : isSimplePower_precond (x) (n)) :=
  -- !benchmark @start postcond
  result = true ↔ (x = 1 ∨ ∃ k, k < x.natAbs + 3 ∧ 1 ≤ k ∧ n ^ k = x)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isSimplePower_spec_satisfied (x : Int) (n : Int) (h_precond : isSimplePower_precond (x) (n)) :
    isSimplePower_postcond (x) (n) (isSimplePower (x) (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
