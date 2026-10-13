# Derivation of verina_advanced_33

kind: **restate**

- **term**: `(let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max 0)`
  - helper lemma `longestIncreasingSubsequence_ok`: `∀ (nums : List Int) (h : longestIncreasingSubsequence_precond nums), longestIncreasingSubsequence_postcond nums (let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max 0) h`
