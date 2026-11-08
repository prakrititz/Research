/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (lst : List (List Int)) (x : Int) (h_precond : getRow_precond lst x) :
    getRow_postcond lst x ((List.range lst.length).flatMap (fun i => ((List.range lst[i]!.length).filter (fun j => (lst[i]!)[j]! == x)).reverse.map (fun j => (i, j)))) h_precond := by
  sorry
