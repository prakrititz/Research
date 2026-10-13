import Mathlib

def maxDepth (l : List Char) : Nat :=
  (((List.range (l.length + 1)).map (fun k => ((l.take k).count '(' : Int) - ((l.take k).count ')' : Int))).foldl max 0).toNat

@[reducible, simp]
def parseNestedParens_precond (paren_string : String) : Prop :=
  paren_string.toList.all (fun c => c == '(' || c == ')' || c == ' ')

@[reducible, simp]
def parseNestedParens_postcond (paren_string : String) (result: List Nat) (h_precond : parseNestedParens_precond (paren_string)) :=
  let groups := (paren_string.splitOn " ").filter (fun g => g != "")
  result.length = groups.length ∧ ∀ i, i < groups.length → result[i]! = maxDepth groups[i]!.toList
