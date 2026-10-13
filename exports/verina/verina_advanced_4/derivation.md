# Derivation of verina_advanced_4

kind: **restate**

- **term**: `(let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max (increasingSubseqLens.headD 0))`
  - helper lemma `LongestIncreasingSubsequence_ok`: `∀ (a : Array Int) (h : LongestIncreasingSubsequence_precond a), LongestIncreasingSubsequence_postcond a (let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length); increasingSubseqLens.foldl max (increasingSubseqLens.headD 0)) h`
