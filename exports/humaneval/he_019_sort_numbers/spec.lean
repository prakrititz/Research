import Mathlib

def numeralNames : List String := ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]
def numeralValue (t : String) : Nat := numeralNames.idxOf t

@[reducible, simp]
def sortNumbers_precond (numbers : String) : Prop :=
  numbers = "" ∨ ∀ t ∈ numbers.splitOn " ", t ∈ numeralNames

@[reducible, simp]
def sortNumbers_postcond (numbers : String) (result: String) (h_precond : sortNumbers_precond (numbers)) :=
  let toks := if numbers = "" then [] else numbers.splitOn " "
  let sorted := if result = "" then [] else result.splitOn " "
  sorted.isPerm toks ∧ ∀ i, i < sorted.length - 1 → numeralValue sorted[i]! ≤ numeralValue sorted[i + 1]!
