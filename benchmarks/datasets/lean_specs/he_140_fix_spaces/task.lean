-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def spaceRun : List Char → Nat
  | ' ' :: t => spaceRun t + 1
  | _ => 0
def fixSpec : Nat → List Char → List Char
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, c :: t =>
    if c = ' ' then
      (if spaceRun (c :: t) ≥ 3 then ['-'] else List.replicate (spaceRun (c :: t)) '_') ++ fixSpec fuel ((c :: t).drop (spaceRun (c :: t)))
    else c :: fixSpec fuel t
-- !benchmark @end precond_aux

@[reducible, simp]
def fixSpaces_precond (text : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def fixSpaces (text : String) (h_precond : fixSpaces_precond (text)) : String :=
  -- !benchmark @start code
  Id.run do
    let mut out : List Char := []
    let mut run : Nat := 0
    for c in text.toList do
      if c == ' ' then
        run := run + 1
      else
        out := out ++ (if run ≥ 3 then ['-'] else List.replicate run '_') ++ [c]
        run := 0
    out := out ++ (if run ≥ 3 then ['-'] else List.replicate run '_')
    return String.mk out
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def fixSpaces_postcond (text : String) (result: String) (h_precond : fixSpaces_precond (text)) :=
  -- !benchmark @start postcond
  result = String.mk (fixSpec text.length text.toList)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem fixSpaces_spec_satisfied (text : String) (h_precond : fixSpaces_precond (text)) :
    fixSpaces_postcond (text) (fixSpaces (text) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
