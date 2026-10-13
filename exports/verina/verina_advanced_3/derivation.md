# Derivation of verina_advanced_3

kind: **restate**

- **term**: `(let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let subseqA := allSubseq a; let subseqB := allSubseq b; let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length); commonSubseqLens.foldl max (commonSubseqLens.headD 0))`
  - helper lemma `LongestCommonSubsequence_ok`: `∀ (a b : Array Int) (h : LongestCommonSubsequence_precond a b), LongestCommonSubsequence_postcond a b (let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let subseqA := allSubseq a; let subseqB := allSubseq b; let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length); commonSubseqLens.foldl max (commonSubseqLens.headD 0)) h`
