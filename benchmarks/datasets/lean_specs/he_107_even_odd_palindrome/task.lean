-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isPal (l : List Char) : Prop := l = l.reverse
-- !benchmark @end precond_aux

@[reducible, simp]
def evenOddPalindrome_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def evenOddPalindrome (n : Nat) (h_precond : evenOddPalindrome_precond (n)) : Nat × Nat :=
  -- !benchmark @start code
  ((List.range (n + 1)).foldl (fun acc i => if 1 ≤ i && (toString i).toList == (toString i).toList.reverse && i % 2 == 0 then acc + 1 else acc) 0,
   (List.range (n + 1)).foldl (fun acc i => if 1 ≤ i && (toString i).toList == (toString i).toList.reverse && i % 2 == 1 then acc + 1 else acc) 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def evenOddPalindrome_postcond (n : Nat) (result: Nat × Nat) (h_precond : evenOddPalindrome_precond (n)) :=
  -- !benchmark @start postcond
  result.1 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0)).length ∧
    result.2 = ((List.range (n + 1)).filter (fun i => 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1)).length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem evenOddPalindrome_spec_satisfied (n : Nat) (h_precond : evenOddPalindrome_precond (n)) :
    evenOddPalindrome_postcond (n) (evenOddPalindrome (n) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
