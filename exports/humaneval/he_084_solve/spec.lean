import Mathlib

@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')

@[reducible, simp]
def solve84_precond (N : Nat) : Prop :=
  True

@[reducible, simp]
def solve84_postcond (N : Nat) (result: String) (h_precond : solve84_precond (N)) :=
  isBinary result.toList (((toString N).toList.map (fun c => c.toNat - '0'.toNat)).sum)
