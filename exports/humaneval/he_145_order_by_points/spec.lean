import Mathlib

def digitWeight (x : Int) : Int :=
  let ds : List Nat := (toString x.natAbs).toList.map (fun c => c.toNat - 48)
  let s : Int := (ds.map (fun d => (d : Int))).sum
  if x < 0 then s - 2 * ((ds.head! : Nat) : Int) else s

@[reducible, simp]
def orderByPoints_precond (nums : List Int) : Prop :=
  True

@[reducible, simp]
def orderByPoints_postcond (nums : List Int) (result: List Int) (h_precond : orderByPoints_precond (nums)) :=
  result.length = nums.length ∧ (∀ i, i < result.length - 1 → digitWeight result[i]! ≤ digitWeight result[i + 1]!) ∧
    ∀ x ∈ nums, result.filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)
