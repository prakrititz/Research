import Mathlib

@[reducible, simp]
def histogram_precond (test : String) : Prop :=
  True

@[reducible, simp]
def histogram_postcond (test : String) (result: List (String × Nat)) (h_precond : histogram_precond (test)) :=
  let ws := (test.splitOn " ").filter (fun w => w != "")
  (ws = [] → result = []) ∧
  (ws ≠ [] → (∀ p ∈ result, p.1 ∈ ws ∧ p.2 = ws.count p.1 ∧ ∀ w ∈ ws, ws.count w ≤ p.2) ∧
    (∀ w ∈ ws, (∀ v ∈ ws, ws.count v ≤ ws.count w) → ∃ p ∈ result, p.1 = w) ∧ (result.map Prod.fst).Nodup)
