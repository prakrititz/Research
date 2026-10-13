import Mathlib

@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')

@[reducible, simp]
def decimalToBinary_precond (decimal : Nat) : Prop :=
  True

@[reducible, simp]
def decimalToBinary_postcond (decimal : Nat) (result: String) (h_precond : decimalToBinary_precond (decimal)) :=
  let l := result.toList
  l.length ≥ 5 ∧ l.take 2 = ['d', 'b'] ∧ l.drop (l.length - 2) = ['d', 'b'] ∧ isBinary ((l.drop 2).take (l.length - 4)) decimal
