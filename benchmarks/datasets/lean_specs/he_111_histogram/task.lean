-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def histogram_precond (test : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def histogram (test : String) (h_precond : histogram_precond (test)) : List (String × Nat) :=
  -- !benchmark @start code
  let ws := (test.splitOn " ").filter (fun w => w != "")
  let best := ws.foldl (fun m w => max m (ws.count w)) 0
  (ws.eraseDups.filter (fun w => ws.count w == best)).map (fun w => (w, ws.count w))
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def histogram_postcond (test : String) (result: List (String × Nat)) (h_precond : histogram_precond (test)) :=
  -- !benchmark @start postcond
  let ws := (test.splitOn " ").filter (fun w => w != "")
  (ws = [] → result = []) ∧
  (ws ≠ [] → (∀ p ∈ result, p.1 ∈ ws ∧ p.2 = ws.count p.1 ∧ ∀ w ∈ ws, ws.count w ≤ p.2) ∧
    (∀ w ∈ ws, (∀ v ∈ ws, ws.count v ≤ ws.count w) → ∃ p ∈ result, p.1 = w) ∧ (result.map Prod.fst).Nodup)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem histogram_spec_satisfied (test : String) (h_precond : histogram_precond (test)) :
    histogram_postcond (test) (histogram (test) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
