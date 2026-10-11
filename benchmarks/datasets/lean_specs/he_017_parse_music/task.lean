-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def parseMusic_precond (music_string : String) : Prop :=
  -- !benchmark @start precond
  music_string = "" ∨ ∀ n ∈ music_string.splitOn " ", n = "o" ∨ n = "o|" ∨ n = ".|"
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def parseMusic (music_string : String) (h_precond : parseMusic_precond (music_string)) : List Nat :=
  -- !benchmark @start code
  ((if music_string = "" then [] else music_string.splitOn " ")).map (fun n => if n = "o" then 4 else if n = "o|" then 2 else 1)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def parseMusic_postcond (music_string : String) (result: List Nat) (h_precond : parseMusic_precond (music_string)) :=
  -- !benchmark @start postcond
  let notes := if music_string = "" then [] else music_string.splitOn " "
  result.length = notes.length ∧ ∀ i, i < notes.length → result[i]! = (if notes[i]! = "o" then 4 else if notes[i]! = "o|" then 2 else 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem parseMusic_spec_satisfied (music_string : String) (h_precond : parseMusic_precond (music_string)) :
    parseMusic_postcond (music_string) (parseMusic (music_string) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
