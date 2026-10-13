import Mathlib

def parseDec (s : String) : ℚ :=
  let neg := s.startsWith "-"
  let body := if neg then String.mk (s.toList.drop 1) else s
  let parts := body.splitOn "."
  let ip := parts[0]!
  let fp := if parts.length > 1 then parts[1]! else ""
  let iv : ℚ := ((ip.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ)
  let fv : ℚ := ((fp.toList.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 : Nat) : ℚ) / 10 ^ fp.length
  (if neg then -1 else 1) * (iv + fv)

@[reducible, simp]
def closestInteger_precond (value : String) : Prop :=
  let body := if value.startsWith "-" then String.mk (value.toList.drop 1) else value
  (body.all (fun c => c.isDigit || c == '.') && (body.toList.filter (fun c => c == '.')).length ≤ 1 && body.toList.any Char.isDigit) = true

@[reducible, simp]
def closestInteger_postcond (value : String) (result: Int) (h_precond : closestInteger_precond (value)) :=
  let q := parseDec value
  |q - (result : ℚ)| < 1 / 2 ∨ (|q - (result : ℚ)| = 1 / 2 ∧ |q| < |(result : ℚ)|)
