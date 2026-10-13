import Mathlib

def seqA (i : Nat) : Nat := i * i - i + 1

@[reducible, simp]
def getMaxTriples_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def getMaxTriples_postcond (n : Nat) (result: Nat) (h_precond : getMaxTriples_precond (n)) :=
  result = ((List.range n).map (fun i => ((List.range n).map (fun j => ((List.range n).filter (fun k => i < j ∧ j < k ∧ (seqA (i + 1) + seqA (j + 1) + seqA (k + 1)) % 3 = 0)).length)).sum)).sum
