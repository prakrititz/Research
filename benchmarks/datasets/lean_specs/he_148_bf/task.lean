-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def solarPlanets : List String := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"]
-- !benchmark @end precond_aux

@[reducible, simp]
def bf_precond (planet1 : String) (planet2 : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def bf (planet1 : String) (planet2 : String) (h_precond : bf_precond (planet1) (planet2)) : List String :=
  -- !benchmark @start code
  if solarPlanets.contains planet1 && solarPlanets.contains planet2 then
    let i := solarPlanets.idxOf planet1
    let j := solarPlanets.idxOf planet2
    (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1)
  else []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def bf_postcond (planet1 : String) (planet2 : String) (result: List String) (h_precond : bf_precond (planet1) (planet2)) :=
  -- !benchmark @start postcond
  (planet1 ∉ solarPlanets ∨ planet2 ∉ solarPlanets → result = []) ∧
    (planet1 ∈ solarPlanets → planet2 ∈ solarPlanets → ∃ i, i < 8 ∧ solarPlanets[i]! = planet1 ∧ ∃ j, j < 8 ∧ solarPlanets[j]! = planet2 ∧
      result = (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem bf_spec_satisfied (planet1 : String) (planet2 : String) (h_precond : bf_precond (planet1) (planet2)) :
    bf_postcond (planet1) (planet2) (bf (planet1) (planet2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
