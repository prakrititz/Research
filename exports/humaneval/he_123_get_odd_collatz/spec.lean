import Mathlib

def collatzSeq : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x ≤ 1 then [1] else x :: collatzSeq fuel (if x % 2 = 0 then x / 2 else 3 * x + 1)

@[reducible, simp]
def getOddCollatz_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def getOddCollatz_postcond (n : Nat) (result: List Nat) (h_precond : getOddCollatz_precond (n)) :=
  result.isPerm ((collatzSeq 5000 n).filter (fun x => x % 2 = 1)) ∧ ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]!
