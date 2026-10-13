import Mathlib

def romanTable : List (Nat × String) := [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"), (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
def romanSpec : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, n =>
    if n = 0 then ""
    else match romanTable.find? (fun p => decide (p.1 ≤ n)) with
      | some p => p.2 ++ romanSpec fuel (n - p.1)
      | none => ""

@[reducible, simp]
def intToMiniRoman_precond (number : Nat) : Prop :=
  1 ≤ number ∧ number ≤ 1000

@[reducible, simp]
def intToMiniRoman_postcond (number : Nat) (result: String) (h_precond : intToMiniRoman_precond (number)) :=
  result = romanSpec number number
