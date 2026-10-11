-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def encChar (c : Char) : Char :=
  let d := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
  if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains d then Char.ofNat (d.toNat + 2) else d
-- !benchmark @end precond_aux

@[reducible, simp]
def encode93_precond (message : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def encode93 (message : String) (h_precond : encode93_precond (message)) : String :=
  -- !benchmark @start code
  String.mk (message.toList.map encChar)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def encode93_postcond (message : String) (result: String) (h_precond : encode93_precond (message)) :=
  -- !benchmark @start postcond
  result.length = message.length ∧ ∀ i, i < message.length → result.toList[i]! = encChar message.toList[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem encode93_spec_satisfied (message : String) (h_precond : encode93_precond (message)) :
    encode93_postcond (message) (encode93 (message) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
