/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
xs : List ℤ
h_precond : moveZeroes_precond xs
⊢ isSubsequence (List.filter (fun x => decide (x ≠ 0)) xs)
      (List.filter (fun x => decide (x ≠ 0)) xs ++ List.filter (fun x => decide (x = 0)) xs) =
    true

case right.left
xs : List ℤ
h_precond : moveZeroes_precond xs
⊢ ((List.dropWhile (fun x => decide (x ≠ 0))
          (List.filter (fun x => decide (x ≠ 0)) xs ++ List.filter (fun x => decide (x = 0)) xs)).all
      fun x => decide (x = 0)) =
    true

case right.right.left
xs : List ℤ
h_precond : moveZeroes_precond xs
⊢ countVal 0 xs = countVal 0 (List.filter (fun x => decide (x ≠ 0)) xs ++ List.filter (fun x => decide (x = 0)) xs)

case right.right.right
xs : List ℤ
h_precond : moveZeroes_precond xs
⊢ xs.length = (List.filter (fun x => decide (x ≠ 0)) xs ++ List.filter (fun x => decide (x = 0)) xs).length
-/
theorem probe (xs : List Int) (h_precond : moveZeroes_precond xs) :
    moveZeroes_postcond xs ((xs.filter (fun x => decide (x ≠ 0))) ++ (xs.filter (fun x => decide (x = 0)))) h_precond := by
  sorry
