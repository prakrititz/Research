/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: the automation hit a Lean resource limit ((deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached); the statement itself is well-formed

unsolved:

-/
theorem probe (test : String) (h_precond : histogram_precond test) :
    histogram_postcond test ((((test.splitOn " ").filter (fun w => w != "")).dedup.filter (fun w => (((test.splitOn " ").filter (fun w => w != "")).count w) == ((((test.splitOn " ").filter (fun w => w != "")).map (fun w => ((test.splitOn " ").filter (fun w => w != "")).count w)).foldl max 0))).map (fun w => (w, ((test.splitOn " ").filter (fun w => w != "")).count w))) h_precond := by
  sorry
