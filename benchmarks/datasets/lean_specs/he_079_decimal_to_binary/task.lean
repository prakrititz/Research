-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')
-- !benchmark @end precond_aux

@[reducible, simp]
def decimalToBinary_precond (decimal : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def decimalToBinary (decimal : Nat) (h_precond : decimalToBinary_precond (decimal)) : String :=
  -- !benchmark @start code
  Id.run do
    let mut m := decimal
    let mut bits := ""
    while m != 0 do
      bits := toString (m % 2) ++ bits
      m := m / 2
    return "db" ++ (if decimal == 0 then "0" else bits) ++ "db"
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def decimalToBinary_postcond (decimal : Nat) (result: String) (h_precond : decimalToBinary_precond (decimal)) :=
  -- !benchmark @start postcond
  let l := result.toList
  l.length ≥ 5 ∧ l.take 2 = ['d', 'b'] ∧ l.drop (l.length - 2) = ['d', 'b'] ∧ isBinary ((l.drop 2).take (l.length - 4)) decimal
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem decimalToBinary_spec_satisfied (decimal : Nat) (h_precond : decimalToBinary_precond (decimal)) :
    decimalToBinary_postcond (decimal) (decimalToBinary (decimal) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
