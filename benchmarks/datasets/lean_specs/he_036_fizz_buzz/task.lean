-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def fizzBuzz_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fizzBuzz (n : Nat) (h_precond : fizzBuzz_precond (n)) : Nat :=
  -- !benchmark @start code
  (List.range n).foldl (fun acc i => if i % 11 == 0 || i % 13 == 0 then acc + (toString i).toList.count '7' else acc) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fizzBuzz_postcond (n : Nat) (result: Nat) (h_precond : fizzBuzz_precond (n)) :=
  -- !benchmark @start postcond
  result = (((List.range n).filter (fun i => i % 11 = 0 ∨ i % 13 = 0)).map (fun i => (toString i).toList.count '7')).sum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fizzBuzz_spec_satisfied (n : Nat) (h_precond : fizzBuzz_precond (n)) :
    fizzBuzz_postcond (n) (fizzBuzz (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
