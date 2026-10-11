-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def polyEval (xs : List Int) (x : ℚ) : ℚ := (List.range xs.length).foldl (fun acc i => acc + ((xs[i]! : Int) : ℚ) * x ^ i) 0
-- !benchmark @end precond_aux

@[reducible, simp]
def findZero_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  xs ≠ [] ∧ xs.length % 2 = 0 ∧ xs.getLast! ≠ 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findZero (xs : List Int) (h_precond : findZero_precond (xs)) : ℚ :=
  -- !benchmark @start code
  let bound : ℚ := 1 + (xs.map (fun c => |(c : ℚ)|)).foldl max 0 / |(xs.getLast! : ℚ)|
  Id.run do
    let mut lo : ℚ := -bound
    let mut hi : ℚ := bound
    let slo := polyEval xs lo
    for _ in [0:80] do
      let mid := (lo + hi) / 2
      if polyEval xs mid * slo ≤ 0 then hi := mid else lo := mid
    return (lo + hi) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findZero_postcond (xs : List Int) (result: ℚ) (h_precond : findZero_precond (xs)) :=
  -- !benchmark @start postcond
  |polyEval xs result| < (1 / 10000 : ℚ)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findZero_spec_satisfied (xs : List Int) (h_precond : findZero_precond (xs)) :
    findZero_postcond (xs) (findZero (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
