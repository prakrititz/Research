import Mathlib

@[reducible, simp]
def antiShuffle_precond (s : String) : Prop :=
  True

@[reducible, simp]
def antiShuffle_postcond (s : String) (result: String) (h_precond : antiShuffle_precond (s)) :=
  let ws := s.splitOn " "
  let rs := result.splitOn " "
  rs.length = ws.length ∧ ∀ i, i < ws.length → rs[i]!.toList.isPerm ws[i]!.toList ∧
    ∀ j, j < rs[i]!.length - 1 → rs[i]!.toList[j]!.toNat ≤ rs[i]!.toList[j + 1]!.toNat
