import Mathlib

def opPrec (o : String) : Nat := if o = "**" then 3 else if o = "*" ∨ o = "//" then 2 else 1
def opApply (o : String) (a b : Int) : Int :=
  if o = "+" then a + b else if o = "-" then a - b else if o = "*" then a * b else if o = "//" then a / b else a ^ b.toNat
def evalOps : Nat → List Int → List String → Int
  | 0, xs, _ => xs.head!
  | fuel + 1, xs, ops =>
    if ops = [] then xs.head! else
      let m := (ops.map opPrec).foldl max 0
      let cands := (List.range ops.length).filter (fun i => opPrec ops[i]! = m)
      let i := if m = 3 then cands.getLast! else cands.head!
      evalOps fuel (xs.take i ++ [opApply ops[i]! xs[i]! xs[i + 1]!] ++ xs.drop (i + 2)) (ops.eraseIdx i)

@[reducible, simp]
def doAlgebra_precond (operator : List String) (operand : List Int) : Prop :=
  operand.length = operator.length + 1 ∧ 2 ≤ operand.length ∧ (∀ x ∈ operand, 0 ≤ x) ∧ ∀ o ∈ operator, o = "+" ∨ o = "-" ∨ o = "*" ∨ o = "//" ∨ o = "**"

@[reducible, simp]
def doAlgebra_postcond (operator : List String) (operand : List Int) (result: Int) (h_precond : doAlgebra_precond (operator) (operand)) :=
  result = evalOps operator.length operand operator
