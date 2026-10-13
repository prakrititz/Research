import Mathlib

def oddDigits (s : String) : Nat := (s.toList.filter (fun c => (c.toNat - 48) % 2 = 1)).length
def oddMsg (n : Nat) : String := "the number of odd elements in the string i of the input.".replace "i" (toString n)

@[reducible, simp]
def oddCount_precond (lst : List String) : Prop :=
  ∀ s ∈ lst, s.toList.all Char.isDigit = true

@[reducible, simp]
def oddCount_postcond (lst : List String) (result: List String) (h_precond : oddCount_precond (lst)) :=
  result.length = lst.length ∧ ∀ k, k < lst.length → result[k]! = oddMsg (oddDigits lst[k]!)
