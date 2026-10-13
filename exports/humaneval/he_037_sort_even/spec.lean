import Mathlib

def atMod (m : Nat) (x : List Int) : List Int := ((List.range x.length).filter (fun i => i % m = 0)).map (fun i => x[i]!)

@[reducible, simp]
def sortEven_precond (l : List Int) : Prop :=
  True

@[reducible, simp]
def sortEven_postcond (l : List Int) (result: List Int) (h_precond : sortEven_precond (l)) :=
  result.length = l.length ∧ (∀ i, i < l.length → i % 2 ≠ 0 → result[i]! = l[i]!) ∧
    (atMod 2 result).isPerm (atMod 2 l) ∧ ∀ i, i < (atMod 2 result).length - 1 → (atMod 2 result)[i]! ≤ (atMod 2 result)[i + 1]!
