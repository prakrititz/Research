-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def rot4 (c : Char) : Char := if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat ((c.toNat - 97 + 4) % 26 + 97) else c
-- !benchmark @end precond_aux

@[reducible, simp]
def encrypt_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def encrypt (s : String) (h_precond : encrypt_precond (s)) : String :=
  -- !benchmark @start code
  String.mk (s.toList.map rot4)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def encrypt_postcond (s : String) (result: String) (h_precond : encrypt_precond (s)) :=
  -- !benchmark @start postcond
  result.length = s.length ∧ ∀ i, i < s.length → result.toList[i]! = rot4 s.toList[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem encrypt_spec_satisfied (s : String) (h_precond : encrypt_precond (s)) :
    encrypt_postcond (s) (encrypt (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
