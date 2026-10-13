import Mathlib

def shiftChar (c : Char) : Char := Char.ofNat ((c.toNat - 97 + 5) % 26 + 97)

@[reducible, simp]
def decodeShift_precond (s : String) : Prop :=
  s.toList.all (fun c => c.isLower) = true

@[reducible, simp]
def decodeShift_postcond (s : String) (result: String) (h_precond : decodeShift_precond (s)) :=
  result.toList.all (fun c => c.isLower) = true ∧ result.toList.map shiftChar = s.toList
