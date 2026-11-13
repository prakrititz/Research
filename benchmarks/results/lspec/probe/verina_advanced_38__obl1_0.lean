/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
intervals : List (ℕ × ℕ)
h_precond : maxCoverageAfterRemovingOne_precond intervals
⊢ maxCoverageAfterRemovingOne_postcond intervals
    (List.foldl max 0
      (List.map
        (fun i =>
          List.foldl (fun acc x => acc + (x.2 - x.1)) 0
            (List.foldl
                (fun acc curr =>
                  match acc with
                  | [] => [curr]
                  | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc)
                [] ((intervals.eraseIdx i).mergeSort fun a b => decide (a.1 ≤ b.1))).reverse)
        (List.range intervals.length)))
    h_precond
-/
theorem probe (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond intervals) :
    maxCoverageAfterRemovingOne_postcond intervals (((List.range intervals.length).map (fun (i : Nat) => let remaining := List.eraseIdx intervals i; let sorted := List.mergeSort remaining (fun (a : Nat × Nat) (b : Nat × Nat) => a.1 ≤ b.1); let merged := sorted.foldl (fun acc curr => match acc with | [] => [curr] | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc) []; merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0)).foldl max 0) h_precond := by
  sorry
