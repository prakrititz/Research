# Derivation of verina_advanced_31

kind: **restate**

- **term**: `(let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max 0)`
  - helper lemma `longestIncreasingSubseqLength_ok`: `∀ (xs : List Int) (h : longestIncreasingSubseqLength_precond xs), longestIncreasingSubseqLength_postcond xs (let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max 0) h`
