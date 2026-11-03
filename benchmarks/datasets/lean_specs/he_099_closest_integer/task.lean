-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def parseDec (s : String) : ℚ :=
  let neg := s.startsWith "-"
  let body := if neg then String.mk (s.toList.drop 1) else s
  let parts := body.splitOn "."
  let ip := parts[0]!
  let fp := if parts.length > 1 then parts[1]! else ""
  let iv : ℚ := ((ip.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ)
  let fv : ℚ := ((fp.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ) / 10 ^ fp.length
  (if neg then -1 else 1) * (iv + fv)
-- !benchmark @end precond_aux

@[reducible, simp]
def closestInteger_precond (value : String) : Prop :=
  -- !benchmark @start precond
  let body := if value.startsWith "-" then String.mk (value.toList.drop 1) else value
  (body.all (fun c => c.isDigit || c == '.') && (body.toList.filter (fun c => c == '.')).length ≤ 1 && body.toList.any Char.isDigit) = true
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def closestInteger (value : String) (h_precond : closestInteger_precond (value)) : Int :=
  -- !benchmark @start code
  let q := parseDec value
  let f := ⌊q⌋
  let frac := q - (f : ℚ)
  if frac < 1 / 2 then f else if frac > 1 / 2 then f + 1 else (if q > 0 then f + 1 else f)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def closestInteger_postcond (value : String) (result: Int) (h_precond : closestInteger_precond (value)) :=
  -- !benchmark @start postcond
  let q := parseDec value
  |q - (result : ℚ)| < 1 / 2 ∨ (|q - (result : ℚ)| = 1 / 2 ∧ |q| < |(result : ℚ)|)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem closestInteger_spec_satisfied (value : String) (h_precond : closestInteger_precond (value)) :
    closestInteger_postcond (value) (closestInteger (value) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
