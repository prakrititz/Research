import Mathlib

@[reducible, simp] def isBinary (m : List Char) (v : Nat) : Prop :=
  m.all (fun c => c == '0' || c == '1') = true ∧ m.foldl (fun acc c => 2 * acc + (if c == '1' then 1 else 0)) 0 = v ∧
    (v = 0 → m = ['0']) ∧ (v > 0 → m.head! = '1')

def roundedHalfEven (s : Nat) : Nat := if s % 2 = 0 then s / 2 else (if (s / 2) % 2 = 0 then s / 2 else s / 2 + 1)

@[reducible, simp]
def roundedAvg_precond (n : Nat) (m : Nat) : Prop :=
  True

@[reducible, simp]
def roundedAvg_postcond (n : Nat) (m : Nat) (result: Option String) (h_precond : roundedAvg_precond (n) (m)) :=
  match result with
  | none => n > m
  | some b => n ≤ m ∧ b.length ≥ 3 ∧ b.toList.take 2 = ['0', 'b'] ∧ isBinary (b.toList.drop 2) (roundedHalfEven (n + m))
