import Mathlib

def encChar (c : Char) : Char :=
  let d := if c.isUpper then c.toLower else if c.isLower then c.toUpper else c
  if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains d then Char.ofNat (d.toNat + 2) else d

@[reducible, simp]
def encode93_precond (message : String) : Prop :=
  True

@[reducible, simp]
def encode93_postcond (message : String) (result: String) (h_precond : encode93_precond (message)) :=
  result.length = message.length ∧ ∀ i, i < message.length → result.toList[i]! = encChar message.toList[i]!
