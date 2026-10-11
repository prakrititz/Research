-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def gridCells (n : Nat) : List (Nat × Nat) := (List.range n).flatMap (fun i => (List.range n).map (fun j => (i, j)))

def stepsFrom (n : Nat) (p : Nat × Nat) : List (Nat × Nat) :=
  (gridCells n).filter (fun q => (q.1 = p.1 ∧ (q.2 = p.2 + 1 ∨ q.2 + 1 = p.2)) ∨ (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ q.1 + 1 = p.1)))

def walksOf (n : Nat) : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | 1 => (gridCells n).map (fun c => [c])
  | k + 2 => (walksOf n (k + 1)).flatMap (fun w => (stepsFrom n w.getLast!).map (fun q => w ++ [q]))

def cellAt (g : List (List Nat)) (p : Nat × Nat) : Nat := (g[p.1]!)[p.2]!
-- !benchmark @end precond_aux

@[reducible, simp]
def minPath_precond (grid : List (List Nat)) (k : Nat) : Prop :=
  -- !benchmark @start precond
  grid.length ≥ 2 ∧ (∀ r ∈ grid, r.length = grid.length) ∧ grid.flatten.isPerm (List.range' 1 (grid.length * grid.length)) ∧ k ≥ 1
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minPath (grid : List (List Nat)) (k : Nat) (h_precond : minPath_precond (grid) (k)) : List Nat :=
  -- !benchmark @start code
  let n := grid.length
  let walks := (walksOf n k).map (fun w => w.map (cellAt grid))
  walks.foldl (fun best w => if w < best then w else best) walks.head!
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minPath_postcond (grid : List (List Nat)) (k : Nat) (result: List Nat) (h_precond : minPath_precond (grid) (k)) :=
  -- !benchmark @start postcond
  (∃ w ∈ walksOf grid.length k, w.map (cellAt grid) = result) ∧ ∀ w ∈ walksOf grid.length k, ¬ (w.map (cellAt grid) < result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minPath_spec_satisfied (grid : List (List Nat)) (k : Nat) (h_precond : minPath_precond (grid) (k)) :
    minPath_postcond (grid) (k) (minPath (grid) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
