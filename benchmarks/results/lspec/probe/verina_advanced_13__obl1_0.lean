/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit (Tactic `simp` failed with a nested error:); the statement itself is well-formed

unsolved:

-/
theorem probe (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond N chords) :
    hasChordIntersection_postcond N chords (let sortedChords := chords.map (fun chord => let a := chord[0]!; let b := chord[1]!; if a > b then [b, a] else [a, b]); sortedChords.any (fun x => sortedChords.any (fun y => hasChordIntersection_postcond.hasIntersection x y))) h_precond := by
  sorry
