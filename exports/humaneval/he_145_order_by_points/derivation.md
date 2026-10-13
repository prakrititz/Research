# Derivation of he_145_order_by_points

kind: **restate**

- **term**: `nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))`
  - helper lemma `order_ok`: `∀ (nums : List Int), (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length = nums.length ∧ (∀ i, i < (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length - 1 → digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i]! ≤ digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i + 1]!) ∧ ∀ x ∈ nums, (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)`
