import Mathlib

@[reducible, simp]
def add_precond (x : Int) (y : Int) : Prop :=
  True

@[reducible, simp]
def add_postcond (x : Int) (y : Int) (result: Int) (h_precond : add_precond (x) (y)) :=
  result = x + y
