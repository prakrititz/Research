import Mathlib

inductive PyVal where
  | int (n : Int)
  | bool (b : Bool)
  | float (q : ℚ)
  | str (s : String)
  | none
  | list (l : List PyVal)
  | dict (d : List (PyVal × PyVal))

def lowerKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isLower && !s.toList.any Char.isUpper
  | _ => false

def upperKey : PyVal → Bool
  | PyVal.str s => s.toList.any Char.isUpper && !s.toList.any Char.isLower
  | _ => false

@[reducible, simp]
def checkDictCase_precond (keys : List PyVal) : Prop :=
  True

@[reducible, simp]
def checkDictCase_postcond (keys : List PyVal) (result: Bool) (h_precond : checkDictCase_precond (keys)) :=
  result = true ↔ (keys ≠ [] ∧ (keys.all lowerKey = true ∨ keys.all upperKey = true))
