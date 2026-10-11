-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def parseQ (s : String) : ℚ :=
  match (s.map (fun c => if c == ',' then '.' else c)).splitOn "." with
  | [w] => (w.toNat! : ℚ)
  | [w, f] => (w.toNat! : ℚ) + (f.toNat! : ℚ) / ((10 : ℚ) ^ f.length)
  | _ => 0
def valQ : ℚ ⊕ String → ℚ
  | Sum.inl q => q
  | Sum.inr s => parseQ s
-- !benchmark @end precond_aux

@[reducible, simp]
def compareOne_precond (a : ℚ ⊕ String) (b : ℚ ⊕ String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def compareOne (a : ℚ ⊕ String) (b : ℚ ⊕ String) (h_precond : compareOne_precond (a) (b)) : Option (ℚ ⊕ String) :=
  -- !benchmark @start code
  if valQ a = valQ b then none else if valQ b < valQ a then some a else some b
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def compareOne_postcond (a : ℚ ⊕ String) (b : ℚ ⊕ String) (result: Option (ℚ ⊕ String)) (h_precond : compareOne_precond (a) (b)) :=
  -- !benchmark @start postcond
  (valQ a = valQ b → result = none) ∧ (valQ b < valQ a → result = some a) ∧ (valQ a < valQ b → result = some b)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem compareOne_spec_satisfied (a : ℚ ⊕ String) (b : ℚ ⊕ String) (h_precond : compareOne_precond (a) (b)) :
    compareOne_postcond (a) (b) (compareOne (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
