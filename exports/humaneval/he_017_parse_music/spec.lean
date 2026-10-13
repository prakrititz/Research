import Mathlib

@[reducible, simp]
def parseMusic_precond (music_string : String) : Prop :=
  music_string = "" ∨ ∀ n ∈ music_string.splitOn " ", n = "o" ∨ n = "o|" ∨ n = ".|"

@[reducible, simp]
def parseMusic_postcond (music_string : String) (result: List Nat) (h_precond : parseMusic_precond (music_string)) :=
  let notes := if music_string = "" then [] else music_string.splitOn " "
  result.length = notes.length ∧ ∀ i, i < notes.length → result[i]! = (if notes[i]! = "o" then 4 else if notes[i]! = "o|" then 2 else 1)
