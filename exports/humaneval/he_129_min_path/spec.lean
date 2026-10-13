import Mathlib

def gridCells (n : Nat) : List (Nat × Nat) := (List.range n).flatMap (fun i => (List.range n).map (fun j => (i, j)))

def stepsFrom (n : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  (gridCells n).filter (fun q => (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ q.2 + 1 = p.2)) ∨ (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ q.1 + 1 = p.1)))

def walksOf (n : Nat) : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | 1 => (gridCells n).map (fun c => [c])
  | k + 2 => (walksOf n (k + 1)).flatMap (fun w => (stepsFrom n w.getLast!).map (fun q => w ++ [q]))

def cellAt (g : List (List Nat)) (p : Nat × Nat) : Nat := (g[p.1]!)[p.2]!

@[reducible, simp]
def minPath_precond (grid : List (List Nat)) (k : Nat) : Prop :=
  grid.length ≥ 2 ∧ (∀ r ∈ grid, r.length = grid.length) ∧ grid.flatten.isPerm (List.range' 1 (grid.length * grid.length)) ∧ k ≥ 1

@[reducible, simp]
def minPath_postcond (grid : List (List Nat)) (k : Nat) (result: List Nat) (h_precond : minPath_precond (grid) (k)) :=
  (∃ w ∈ walksOf grid.length k, w.map (cellAt grid) = result) ∧ ∀ w ∈ walksOf grid.length k, ¬ (w.map (cellAt grid) < result)
