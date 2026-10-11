-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def stringXor_precond (a : String) (b : String) : Prop :=
  -- !benchmark @start precond
  a.length = b.length ∧ a.toList.all (fun c => c == '0' || c == '1') ∧ b.toList.all (fun c => c == '0' || c == '1')
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def stringXor (a : String) (b : String) (h_precond : stringXor_precond (a) (b)) : String :=
  -- !benchmark @start code
  String.mk ((a.toList.zip b.toList).map (fun p => if p.1 = p.2 then '0' else '1'))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def stringXor_postcond (a : String) (b : String) (result: String) (h_precond : stringXor_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.length = a.length ∧ ∀ i, i < a.length → result.toList[i]! = (if a.toList[i]! = b.toList[i]! then '0' else '1')
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem stringXor_spec_satisfied (a : String) (b : String) (h_precond : stringXor_precond (a) (b)) :
    stringXor_postcond (a) (b) (stringXor (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
