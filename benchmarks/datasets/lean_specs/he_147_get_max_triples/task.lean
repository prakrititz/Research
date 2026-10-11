-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def seqA (i : Nat) : Nat := i * i - i + 1
-- !benchmark @end precond_aux

@[reducible, simp]
def getMaxTriples_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def getMaxTriples (n : Nat) (h_precond : getMaxTriples_precond (n)) : Nat :=
  -- !benchmark @start code
  if n ≤ 2 then 0 else
    let one := 1 + (n - 2) / 3 * 2 + (n - 2) % 3
    let zero := n - one
    one * (one - 1) * (one - 2) / 6 + zero * (zero - 1) * (zero - 2) / 6
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def getMaxTriples_postcond (n : Nat) (result: Nat) (h_precond : getMaxTriples_precond (n)) :=
  -- !benchmark @start postcond
  result = ((List.range n).map (fun i => ((List.range n).map (fun j => ((List.range n).filter (fun k => i < j ∧ j < k ∧ (seqA (i + 1) + seqA (j + 1) + seqA (k + 1)) % 3 = 0)).length)).sum)).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem getMaxTriples_spec_satisfied (n : Nat) (h_precond : getMaxTriples_precond (n)) :
    getMaxTriples_postcond (n) (getMaxTriples (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
