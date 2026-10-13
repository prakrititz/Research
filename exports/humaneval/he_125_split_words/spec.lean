import Mathlib

def splitWhite (txt : String) : List String :=
  ((txt.map (fun c => if c == '\n' || c == '\r' || c == '\t' then ' ' else c)).splitOn " ").filter (fun w => w != "")

@[reducible, simp]
def splitWords_precond (txt : String) : Prop :=
  True

@[reducible, simp]
def splitWords_postcond (txt : String) (result: List String ⊕ Nat) (h_precond : splitWords_precond (txt)) :=
  let hasWhite := txt.toList.any (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')
  result = (if hasWhite then Sum.inl (splitWhite txt)
    else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",")
    else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 = 1)).length))
