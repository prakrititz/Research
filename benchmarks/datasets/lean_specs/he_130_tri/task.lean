-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def tri_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def tri (n : Nat) (h_precond : tri_precond (n)) : List Nat :=
  -- !benchmark @start code
  Id.run do
    let mut ans : List Nat := [1, 3]
    if n == 0 then return [1]
    for i in [2:n + 1] do
      if i % 2 == 0 then ans := ans ++ [1 + i / 2]
      else ans := ans ++ [ans[i - 1]! + ans[i - 2]! + 1 + (i + 1) / 2]
    return ans
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def tri_postcond (n : Nat) (result: List Nat) (h_precond : tri_precond (n)) :=
  -- !benchmark @start postcond
  result.length = n + 1 ∧ result[0]! = 1 ∧ (n ≥ 1 → result[1]! = 3) ∧
    ∀ i, i < n + 1 → 2 ≤ i → result[i]! = (if i % 2 = 0 then 1 + i / 2 else result[i - 1]! + result[i - 2]! + (1 + (i + 1) / 2))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem tri_spec_satisfied (n : Nat) (h_precond : tri_precond (n)) :
    tri_postcond (n) (tri (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
