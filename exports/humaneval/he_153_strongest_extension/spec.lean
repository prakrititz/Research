import Mathlib

def strength (s : String) : Int := ((s.toList.filter Char.isUpper).length : Int) - ((s.toList.filter Char.isLower).length : Int)

@[reducible, simp]
def strongestExtension_precond (class_name : String) (extensions : List String) : Prop :=
  extensions ≠ []

@[reducible, simp]
def strongestExtension_postcond (class_name : String) (extensions : List String) (result: String) (h_precond : strongestExtension_precond (class_name) (extensions)) :=
  ∃ i, i < extensions.length ∧ result = class_name ++ "." ++ extensions[i]! ∧
    (∀ j, j < extensions.length → strength extensions[j]! ≤ strength extensions[i]!) ∧ ∀ j, j < i → strength extensions[j]! < strength extensions[i]!
