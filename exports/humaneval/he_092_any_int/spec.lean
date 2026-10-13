import Mathlib

inductive PyVal where
  | int (n : Int)
  | bool (b : Bool)
  | float (q : ℚ)
  | str (s : String)
  | none
  | list (l : List PyVal)
  | dict (d : List (PyVal × PyVal))

@[reducible, simp]
def anyInt_precond (x : PyVal) (y : PyVal) (z : PyVal) : Prop :=
  True

@[reducible, simp]
def anyInt_postcond (x : PyVal) (y : PyVal) (z : PyVal) (result: Bool) (h_precond : anyInt_precond (x) (y) (z)) :=
  result = true ↔ (match x, y, z with
    | PyVal.int a, PyVal.int b, PyVal.int c => a = b + c ∨ b = a + c ∨ c = b + a
    | _, _, _ => False)
