import Mathlib

@[reducible, simp]
def sqrtApprox_precond (N : ℚ) (e : ℚ) : Prop :=
  N ≥ 0 ∧ e > 0

@[reducible, simp]
def sqrtApprox_postcond (N : ℚ) (e : ℚ) (result: ℚ) (h_precond : sqrtApprox_precond (N) (e)) :=
  result ≥ 0 ∧ result * result ≤ N ∧ N < (result + e) * (result + e)
