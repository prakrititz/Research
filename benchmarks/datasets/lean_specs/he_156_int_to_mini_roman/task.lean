-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def romanTable : List (Nat × String) := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
def romanSpec : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n =>
    if n = 0 then ""
    else match romanTable.find? (fun p => decide (p.1 ≤ n)) with
      | some p => p.2 ++ romanSpec fuel (n - p.1)
      | none => ""
-- !benchmark @end precond_aux

@[reducible, simp]
def intToMiniRoman_precond (number : Nat) : Prop :=
  -- !benchmark @start precond
  1 ≤ number ∧ number ≤ 1000
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def intToMiniRoman (number : Nat) (h_precond : intToMiniRoman_precond (number)) : String :=
  -- !benchmark @start code
  let thousands := ["", "m"]
  let hundreds := ["", "c", "cc", "ccc", "cd", "d", "dc", "dcc", "dccc", "cm"]
  let tens := ["", "x", "xx", "xxx", "xl", "l", "lx", "lxx", "lxxx", "xc"]
  let ones := ["", "i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix"]
  thousands[number / 1000]! ++ hundreds[(number % 1000) / 100]! ++ tens[(number % 100) / 10]! ++ ones[number % 10]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def intToMiniRoman_postcond (number : Nat) (result: String) (h_precond : intToMiniRoman_precond (number)) :=
  -- !benchmark @start postcond
  result = romanSpec number number
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem intToMiniRoman_spec_satisfied (number : Nat) (h_precond : intToMiniRoman_precond (number)) :
    intToMiniRoman_postcond (number) (intToMiniRoman (number) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
