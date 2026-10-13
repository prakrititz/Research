# Derivation of he_129_min_path

kind: **restate**

- **term**: `((walksOf grid.length k).map (fun w => w.map (cellAt grid))).foldl (fun b c => if c < b then c else b) ((walksOf grid.length k).map (fun w => w.map (cellAt grid))).head!`
  - helper lemma `lexmin_facts`: `∀ (L : List (List Nat)) (init : List Nat) (seen : List (List Nat)), (∀ c ∈ seen, ¬ c < init) → (∀ c ∈ seen ++ L, ¬ c < List.foldl (fun b c => if c < b then c else b) init L) ∧ (List.foldl (fun b c => if c < b then c else b) init L = init ∨ List.foldl (fun b c => if c < b then c else b) init L ∈ L)`
  - helper lemma `grid_mem`: `∀ (n i j : Nat), (i, j) ∈ gridCells n ↔ i < n ∧ j < n`
  - helper lemma `steps_ne`: `∀ (n : Nat), 2 ≤ n → ∀ (p : Nat × Nat), p ∈ gridCells n → stepsFrom n p ≠ []`
  - helper lemma `walks_ok`: `∀ (n : Nat), 2 ≤ n → ∀ (k : Nat), walksOf n (k + 1) ≠ [] ∧ ∀ w ∈ walksOf n (k + 1), w ≠ [] ∧ w.getLast! ∈ gridCells n`
  - helper lemma `min_path_post`: `∀ (grid : List (List Nat)) (k : Nat) (h : minPath_precond grid k), minPath_postcond grid k (((walksOf grid.length k).map (fun w => w.map (cellAt grid))).foldl (fun b c => if c < b then c else b) ((walksOf grid.length k).map (fun w => w.map (cellAt grid))).head!) h`
