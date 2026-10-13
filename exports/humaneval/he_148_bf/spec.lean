import Mathlib

def solarPlanets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]

@[reducible, simp]
def bf_precond (planet1 : String) (planet2 : String) : Prop :=
  True

@[reducible, simp]
def bf_postcond (planet1 : String) (planet2 : String) (result: List String) (h_precond : bf_precond (planet1) (planet2)) :=
  (planet1 ∉ solarPlanets ∨ planet2 ∉ solarPlanets → result = []) ∧
    (planet1 ∈ solarPlanets → planet2 ∈ solarPlanets → ∃ i, i < 8 ∧ solarPlanets[i]! = planet1 ∧ ∃ j, j < 8 ∧ solarPlanets[j]! = planet2 ∧
      result = (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1))
