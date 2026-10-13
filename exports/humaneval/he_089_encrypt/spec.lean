import Mathlib

def rot4 (c : Char) : Char := if 'a' ≤ c ∧ c ≤ 'z' then Char.ofNat ((c.toNat - 97 + 4) % 26 + 97) else c

@[reducible, simp]
def encrypt_precond (s : String) : Prop :=
  True

@[reducible, simp]
def encrypt_postcond (s : String) (result: String) (h_precond : encrypt_precond (s)) :=
  result.length = s.length ∧ ∀ i, i < s.length → result.toList[i]! = rot4 s.toList[i]!
