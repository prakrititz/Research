-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def changeBase_precond (x : Nat) (base : Nat) : Prop :=
  -- !benchmark @start precond
  2 ≤ base ∧ base < 10
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def changeBase (x : Nat) (base : Nat) (h_precond : changeBase_precond (x) (base)) : String :=
  -- !benchmark @start code
  Id.run do
    let mut m := x
    let mut ret := ""
    while m != 0 do
      ret := toString (m % base) ++ ret
      m := m / base
    return (if x == 0 then "0" else ret)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def changeBase_postcond (x : Nat) (base : Nat) (result: String) (h_precond : changeBase_precond (x) (base)) :=
  -- !benchmark @start postcond
  result.toList.all (fun c => c.isDigit && c.toNat - '0'.toNat < base) = true ∧
    result.toList.foldl (fun acc c => acc * base + (c.toNat - '0'.toNat)) 0 = x ∧
    (x = 0 → result = "0") ∧ (x > 0 → result.toList.head! ≠ '0')
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem changeBase_spec_satisfied (x : Nat) (base : Nat) (h_precond : changeBase_precond (x) (base)) :
    changeBase_postcond (x) (base) (changeBase (x) (base) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
