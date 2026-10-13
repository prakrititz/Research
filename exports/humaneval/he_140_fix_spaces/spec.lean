import Mathlib

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

@[reducible, simp]
def fixSpaces_precond (text : String) : Prop :=
  True

@[reducible, simp]
def fixSpaces_postcond (text : String) (result: String) (h_precond : fixSpaces_precond (text)) :=
  result = String.mk (fixSpec text.length text.toList)
