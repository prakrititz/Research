-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def collatzSeq : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x ≤ 1 then [1] else x :: collatzSeq fuel (if x % 2 = 0 then x / 2 else 3 * x + 1)
-- !benchmark @end precond_aux

@[reducible, simp]
def getOddCollatz_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def getOddCollatz (n : Nat) (h_precond : getOddCollatz_precond (n)) : List Nat :=
  -- !benchmark @start code
  ((collatzSeq 5000 n).filter (fun x => x % 2 = 1)).mergeSort (fun a b => a ≤ b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def getOddCollatz_postcond (n : Nat) (result: List Nat) (h_precond : getOddCollatz_precond (n)) :=
  -- !benchmark @start postcond
  result.isPerm ((collatzSeq 5000 n).filter (fun x => x % 2 = 1)) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem getOddCollatz_spec_satisfied (n : Nat) (h_precond : getOddCollatz_precond (n)) :
    getOddCollatz_postcond (n) (getOddCollatz (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
