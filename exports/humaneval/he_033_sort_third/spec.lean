import Mathlib

def atMod (m : Nat) (x : List Int) : List Int := ((List.range x.length).filter (fun i => i % m = 0)).map (fun i => x[i]!)

@[reducible, simp]
def sortThird_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def sortThird_postcond (l : List Int) (result: List Int) (h_precond : sortThird_precond (l)) :=
  result.length = l.length ∧ (∀ i, i < l.length → i % 3 ≠ 0 → result[i]! = l[i]!) ∧
    (atMod 3 result).isPerm (atMod 3 l) ∧ ∀ i, i < (atMod 3 result).length - 1 → (atMod 3 result)[i]! ≤ (atMod 3 result)[i + 1]!
