import Mathlib

@[reducible, simp]
def compareGuess_precond (game : List Int) (guess : List Int) : Prop :=
  game.length = guess.length

@[reducible, simp]
def compareGuess_postcond (game : List Int) (guess : List Int) (result: List Int) (h_precond : compareGuess_precond (game) (guess)) :=
  result.length = game.length ∧ ∀ i, i < game.length → result[i]! = ((game[i]! - guess[i]!).natAbs : Int)
