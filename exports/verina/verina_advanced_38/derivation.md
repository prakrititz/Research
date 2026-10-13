# Derivation of verina_advanced_38

kind: **restate**

- **term**: `((List.range intervals.length).map (fun (i : Nat) => let remaining := List.eraseIdx intervals i; let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1); let merged := sorted.foldl (fun acc curr => match acc with | [] => [curr] | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc) []; merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0)).foldl max 0`
  - helper lemma `argmax_spec`: `∀ (n : Nat) (f : Nat → Nat), 0 < n → ∃ i, i < n ∧ f i = ((List.range n).map f).foldl max 0 ∧ ∀ j, j < n → f j ≤ ((List.range n).map f).foldl max 0`
  - helper lemma `mc38`: `∀ (intervals : List (Prod Nat Nat)) (h : maxCoverageAfterRemovingOne_precond intervals), maxCoverageAfterRemovingOne_postcond intervals (((List.range intervals.length).map (fun (i : Nat) => let remaining := List.eraseIdx intervals i; let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1); let merged := sorted.foldl (fun acc curr => match acc with | [] => [curr] | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc) []; merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0)).foldl max 0) h`
