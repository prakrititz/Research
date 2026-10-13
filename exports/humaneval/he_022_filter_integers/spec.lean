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
def filterIntegers_precond (values : List PyVal) : Prop :=
  True

@[reducible, simp]
def filterIntegers_postcond (values : List PyVal) (result: List Int) (h_precond : filterIntegers_precond (values)) :=
  result = values.filterMap (fun v => match v with | PyVal.int n => some n | _ => none)
