/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case right.left
nums : List ℤ
k : ℕ
h_precond : topKFrequent_precond nums k
⊢ ((List.take k (nums.eraseDups.mergeSort fun x y => decide (List.count y nums ≤ List.count x nums))).all fun x =>
      decide (x ∈ nums)) =
    true

case right.right.left
nums : List ℤ
k : ℕ
h_precond : topKFrequent_precond nums k
⊢ List.Pairwise (fun x1 x2 => x1 ≠ x2)
    (List.take k (nums.eraseDups.mergeSort fun x y => decide (List.count y nums ≤ List.count x nums)))

case right.right.right.left
nums : List ℤ
k : ℕ
h_precond : topKFrequent_precond nums k
⊢ ((List.take k (nums.eraseDups.mergeSort fun x y => decide (List.count y nums ≤ List.count x nums))).all fun x =>
      nums.all fun y =>
        decide
          (y ∈ List.take k (nums.eraseDups.mergeSort fun x y => decide (List.count y nums ≤ List.count x nums)) ∨
            List.count x nums ≥ List.count y nums)) =
    true

case right.right.right.right
nums : List ℤ
k : ℕ
h_precond : topKFrequent_precond nums k
⊢ List.Pairwise
    (fun x x_1 =>
      match x with
      | (x, i) =>
        match x_1 with
        | (y, j) => i < j → List.count x nums ≥ List.count y nums)
    (List.take k (nums.eraseDups.mergeSort fun x y => decide (List.count y nums ≤ List.count x nums))).zipIdx
-/
theorem probe (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond nums k) :
    topKFrequent_postcond nums k ((nums.eraseDups.mergeSort (fun x y => decide ((nums.count y) ≤ (nums.count x)))).take k) h_precond := by
  sorry
