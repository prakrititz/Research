-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def compareGuess_precond (game : List Int) (guess : List Int) : Prop :=
  -- !benchmark @start precond
  game.length = guess.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def compareGuess (game : List Int) (guess : List Int) (h_precond : compareGuess_precond (game) (guess)) : List Int :=
  -- !benchmark @start code
  (game.zip guess).map (fun (g, s) => ((g - s).natAbs : Int))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def compareGuess_postcond (game : List Int) (guess : List Int) (result: List Int) (h_precond : compareGuess_precond (game) (guess)) :=
  -- !benchmark @start postcond
  result.length = game.length ∧ ∀ i, i < game.length → result[i]! = ((game[i]! - guess[i]!).natAbs : Int)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem compareGuess_spec_satisfied (game : List Int) (guess : List Int) (h_precond : compareGuess_precond (game) (guess)) :
    compareGuess_postcond (game) (guess) (compareGuess (game) (guess) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
