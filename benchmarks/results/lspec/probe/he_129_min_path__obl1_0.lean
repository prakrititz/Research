/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case left
grid : List (List ℕ)
k : ℕ
h_precond : minPath_precond grid k
⊢ ∃ w ∈ walksOf grid.length k,
    List.map (cellAt grid) w =
      List.foldl (fun b c => if c < b then c else b)
        (List.map (fun w => List.map (cellAt grid) w) (walksOf grid.length k)).head!
        (List.map (fun w => List.map (cellAt grid) w) (walksOf grid.length k))

case right
grid : List (List ℕ)
k : ℕ
h_precond : minPath_precond grid k
⊢ ∀ w ∈ walksOf grid.length k,
    ¬List.map (cellAt grid) w <
        List.foldl (fun b c => if c < b then c else b)
          (List.map (fun w => List.map (cellAt grid) w) (walksOf grid.length k)).head!
          (List.map (fun w => List.map (cellAt grid) w) (walksOf grid.length k))
-/
theorem probe (grid : List (List Nat)) (k : Nat) (h_precond : minPath_precond grid k) :
    minPath_postcond grid k (((walksOf grid.length k).map (fun w => w.map (cellAt grid))).foldl (fun b c => if c < b then c else b) ((walksOf grid.length k).map (fun w => w.map (cellAt grid))).head!) h_precond := by
  sorry
