example (arr : List ℤ) (k : ℕ) : ((List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse.isPerm
      (List.take k (arr.mergeSort fun a b => decide (a ≥ b)))) = true := by simp [Refine.reverse_isPerm]
example (arr : List ℤ) (k : ℕ) : ∀ i < (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse.length - 1,
    (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse[i]! ≤
      (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse[i + 1]! := by
  apply Refine.sorted_reverse_take_mergeSort_ge
@[reducible, simp] def IsPalindrome_postcond (x : List Char) (result: Bool) := result ↔ ∀ i : Nat, i < x.length → (x[i]! = x[x.length - i - 1]!)
example (x : List Char) : IsPalindrome_postcond x (x.reverse == x) := by
  simp only [IsPalindrome_postcond, beq_iff_eq]; apply Refine.reverse_eq_self_iff_idx
example (x : List Char) : IsPalindrome_postcond x (x.reverse == x) := by
  simp_all; apply Refine.reverse_eq_self_iff_idx'
example (x : List Char) : IsPalindrome_postcond x (x.reverse == x) := by
  unfold IsPalindrome_postcond; apply Refine.reverse_beq_self_iff_idx
def ones (x : Int) : Nat := ((Nat.digits 2 x.natAbs).filter (fun d => d == 1)).length
example (arr : List ℤ) : ∀ i < (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b)).length - 1,
    ones (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i]! <
        ones (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i + 1]! ∨
      ones (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i]! =
          ones (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i + 1]! ∧
        (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i]! ≤
          (arr.mergeSort fun a b => decide (ones a < ones b) || ones a == ones b && decide (a ≤ b))[i + 1]! := by
  intros; apply Refine.mergeSort_key_then_le; assumption
