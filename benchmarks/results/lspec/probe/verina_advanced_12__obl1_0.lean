/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
lst : List ℤ
h_precond : firstDuplicate_precond lst
⊢ firstDuplicate_postcond lst
    (@obl1_0.match_1 (fun x => Option ℤ) (List.filter (fun y => decide (List.count y lst > 1)) lst) (fun _ => none)
      fun b t =>
      some (List.foldl (fun best y => if secondOccIdx lst y < secondOccIdx lst best then y else best) b (b :: t)))
    h_precond
-/
theorem probe (lst : List Int) (h_precond : firstDuplicate_precond lst) :
    firstDuplicate_postcond lst (match lst.filter (fun y => decide ((lst.count y) > 1)) with | [] => none | b :: t => some ((b :: t).foldl (fun best y => if (secondOccIdx lst y) < (secondOccIdx lst best) then y else best) b)) h_precond := by
  sorry
