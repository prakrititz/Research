-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rescaleToUnit_precond (numbers : List ℚ) : Prop :=
  -- !benchmark @start precond
  numbers.length ≥ 2 ∧ numbers.foldl min numbers[0]! < numbers.foldl max numbers[0]!
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rescaleToUnit (numbers : List ℚ) (h_precond : rescaleToUnit_precond (numbers)) : List ℚ :=
  -- !benchmark @start code
  let mi := numbers.foldl min numbers[0]!
  let ma := numbers.foldl max numbers[0]!
  numbers.map (fun x => (x - mi) / (ma - mi))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rescaleToUnit_postcond (numbers : List ℚ) (result: List ℚ) (h_precond : rescaleToUnit_precond (numbers)) :=
  -- !benchmark @start postcond
  result.length = numbers.length ∧ ∀ i, i < numbers.length →
      |result[i]! - (numbers[i]! - numbers.foldl min numbers[0]!) / (numbers.foldl max numbers[0]! - numbers.foldl min numbers[0]!)| ≤ (1 / 1000000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rescaleToUnit_spec_satisfied (numbers : List ℚ) (h_precond : rescaleToUnit_precond (numbers)) :
    rescaleToUnit_postcond (numbers) (rescaleToUnit (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
