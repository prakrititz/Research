import Mathlib

@[reducible, simp]
def intersection_precond (interval1 : Int × Int) (interval2 : Int × Int) : Prop :=
  interval1.1 ≤ interval1.2 ∧ interval2.1 ≤ interval2.2

@[reducible, simp]
def intersection_postcond (interval1 : Int × Int) (interval2 : Int × Int) (result: String) (h_precond : intersection_precond (interval1) (interval2)) :=
  let len := min interval1.2 interval2.2 - max interval1.1 interval2.1
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ (len ≥ 2 ∧ Nat.Prime len.toNat))
