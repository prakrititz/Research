import Mathlib

@[reducible, simp]
def canArrange_precond (arr : List Int) : Prop :=
  arr.Nodup

@[reducible, simp]
def canArrange_postcond (arr : List Int) (result: Int) (h_precond : canArrange_precond (arr)) :=
  (result = -1 ∧ ∀ i, i < arr.length → 1 ≤ i → arr[i - 1]! ≤ arr[i]!) ∨
    (∃ i, i < arr.length ∧ 1 ≤ i ∧ result = (i : Int) ∧ arr[i]! < arr[i - 1]! ∧ ∀ j, j < arr.length → i < j → arr[j - 1]! ≤ arr[j]!)
