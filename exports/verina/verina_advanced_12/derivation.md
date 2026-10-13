# Derivation of verina_advanced_12

kind: **restate**

- **term**: `(match lst.filter (fun y => decide (lst.count y > 1)) with | [] => none | b :: t => some ((b :: t).foldl (fun best y => if secondOccIdx lst y < secondOccIdx lst best then y else best) b))`
  - helper lemma `argmin_facts`: `∀ {α : Type} (f : α → Nat) (L : List α) (b : α), (L.foldl (fun best y => if f y < f best then y else best) b = b ∨ L.foldl (fun best y => if f y < f best then y else best) b ∈ L) ∧ f (L.foldl (fun best y => if f y < f best then y else best) b) ≤ f b ∧ ∀ y ∈ L, f (L.foldl (fun best y => if f y < f best then y else best) b) ≤ f y`
  - helper lemma `first12`: `∀ (lst : List Int) (h : firstDuplicate_precond lst), firstDuplicate_postcond lst (match lst.filter (fun y => decide (lst.count y > 1)) with | [] => none | b :: t => some ((b :: t).foldl (fun best y => if secondOccIdx lst y < secondOccIdx lst best then y else best) b)) h`
