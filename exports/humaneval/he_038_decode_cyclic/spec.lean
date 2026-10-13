import Mathlib

def encodeGroups : List Char → List Char
  | a :: b :: c :: rest => b :: c :: a :: encodeGroups rest
  | l => l

@[reducible, simp]
def decodeCyclic_precond (s : String) : Prop :=
  True

@[reducible, simp]
def decodeCyclic_postcond (s : String) (result: String) (h_precond : decodeCyclic_precond (s)) :=
  encodeGroups result.toList = s.toList
