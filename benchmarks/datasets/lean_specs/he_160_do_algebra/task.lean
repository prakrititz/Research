-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
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
-- !benchmark @end precond_aux

@[reducible, simp]
def doAlgebra_precond (operator : List String) (operand : List Int) : Prop :=
  -- !benchmark @start precond
  operand.length = operator.length + 1 ∧ 2 ≤ operand.length ∧ (∀ x ∈ operand, 0 ≤ x) ∧ ∀ o ∈ operator, o = "+" ∨ o = "-" ∨ o = "*" ∨ o = "//" ∨ o = "**"
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def doAlgebra (operator : List String) (operand : List Int) (h_precond : doAlgebra_precond (operator) (operand)) : Int :=
  -- !benchmark @start code
  evalOps operator.length operand operator
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def doAlgebra_postcond (operator : List String) (operand : List Int) (result: Int) (h_precond : doAlgebra_precond (operator) (operand)) :=
  -- !benchmark @start postcond
  result = evalOps operator.length operand operator
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem doAlgebra_spec_satisfied (operator : List String) (operand : List Int) (h_precond : doAlgebra_precond (operator) (operand)) :
    doAlgebra_postcond (operator) (operand) (doAlgebra (operator) (operand) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
