-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def wordsInSentence_precond (sentence : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def wordsInSentence (sentence : String) (h_precond : wordsInSentence_precond (sentence)) : String :=
  -- !benchmark @start code
  " ".intercalate ((sentence.splitOn " ").filter (fun w => w.length ≥ 2 && (List.range w.length).all (fun d => d < 2 || w.length % d != 0)))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def wordsInSentence_postcond (sentence : String) (result: String) (h_precond : wordsInSentence_precond (sentence)) :=
  -- !benchmark @start postcond
  result = " ".intercalate ((sentence.splitOn " ").filter (fun w => decide (Nat.Prime w.length)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem wordsInSentence_spec_satisfied (sentence : String) (h_precond : wordsInSentence_precond (sentence)) :
    wordsInSentence_postcond (sentence) (wordsInSentence (sentence) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
