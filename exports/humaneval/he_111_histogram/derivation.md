# Derivation of he_111_histogram

kind: **restate**

- **term**: `(((test.splitOn " ").filter (fun w => w != "")).dedup.filter (fun w => ((test.splitOn " ").filter (fun w => w != "")).count w == (((test.splitOn " ").filter (fun w => w != "")).map (fun w => ((test.splitOn " ").filter (fun w => w != "")).count w)).foldl max 0)).map (fun w => (w, ((test.splitOn " ").filter (fun w => w != "")).count w))`
  - helper lemma `foldl_max_nat`: `∀ (l : List Nat) (m : Nat), (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l`
  - helper lemma `hist_ok`: `∀ (ws : List String), ((ws = [] → ((ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w))) = []) ∧ (ws ≠ [] → (∀ p ∈ (ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w)), p.1 ∈ ws ∧ p.2 = ws.count p.1 ∧ ∀ w ∈ ws, ws.count w ≤ p.2) ∧ (∀ w ∈ ws, (∀ v ∈ ws, ws.count v ≤ ws.count w) → ∃ p ∈ (ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w)), p.1 = w) ∧ (((ws.dedup.filter (fun w => ws.count w == (ws.map (fun w => ws.count w)).foldl max 0)).map (fun w => (w, ws.count w))).map Prod.fst).Nodup))`
