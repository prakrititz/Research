-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def antiShuffle_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def antiShuffle (s : String) (h_precond : antiShuffle_precond (s)) : String :=
  -- !benchmark @start code
  " ".intercalate ((s.splitOn " ").map (fun w => String.mk (w.toList.mergeSort (fun a b => a.toNat ≤ b.toNat))))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def antiShuffle_postcond (s : String) (result: String) (h_precond : antiShuffle_precond (s)) :=
  -- !benchmark @start postcond
  let ws := s.splitOn " "
  let rs := result.splitOn " "
  rs.length = ws.length ∧ ∀ i, i < ws.length → rs[i]!.toList.isPerm ws[i]!.toList ∧
    ∀ j, j < rs[i]!.length - 1 → rs[i]!.toList[j]!.toNat ≤ rs[i]!.toList[j + 1]!.toNat
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem antiShuffle_spec_satisfied (s : String) (h_precond : antiShuffle_precond (s)) :
    antiShuffle_postcond (s) (antiShuffle (s) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
