# Derivation of verina_advanced_55

kind: **restate**

- **term**: `((xs.find? (fun x => decide (xs.countP (fun y => y = x) = (xs.map (fun x => xs.countP (fun y => y = x))).foldl max 0))).getD 0)`
  - helper lemma `most55_a`: `∀ (xs : List Int) (h : mostFrequent_precond xs) (r : Int), r ∈ xs → (∀ x, x ∈ xs → xs.countP (fun y => y = x) ≤ xs.countP (fun y => y = r)) → xs.find? (fun x => decide (xs.countP (fun y => y = x) = xs.countP (fun y => y = r))) = some r → mostFrequent_postcond xs r h`
  - helper lemma `most55`: `∀ (xs : List Int) (h : mostFrequent_precond xs), mostFrequent_postcond xs ((xs.find? (fun x => decide (xs.countP (fun y => y = x) = (xs.map (fun x => xs.countP (fun y => y = x))).foldl max 0))).getD 0) h`
