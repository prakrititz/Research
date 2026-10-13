import Mathlib

@[reducible, simp]
def willItFly_precond (q : List Int) (w : Int) : Prop :=
  True

@[reducible, simp]
def willItFly_postcond (q : List Int) (w : Int) (result: Bool) (h_precond : willItFly_precond (q) (w)) :=
  result = true ↔ ((∀ i, i < q.length → q[i]! = q[q.length - 1 - i]!) ∧ q.sum ≤ w)
