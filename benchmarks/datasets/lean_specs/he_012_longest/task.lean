-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def longest_precond (strings : List String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longest (strings : List String) (h_precond : longest_precond (strings)) : Option String :=
  -- !benchmark @start code
  strings.foldl (fun acc s => match acc with
    | none => some s
    | some b => if s.length > b.length then some s else some b) none
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def longest_postcond (strings : List String) (result: Option String) (h_precond : longest_precond (strings)) :=
  -- !benchmark @start postcond
  match result with
    | none => strings = []
    | some s => ∃ i, i < strings.length ∧ strings[i]! = s ∧ (∀ t ∈ strings, t.length ≤ s.length) ∧
        ∀ j, j < i → strings[j]!.length < s.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longest_spec_satisfied (strings : List String) (h_precond : longest_precond (strings)) :
    longest_postcond (strings) (longest (strings) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
