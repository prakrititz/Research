# Derivation of verina_advanced_27

kind: **restate**

- **term**: `(let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let subseqA := allSubseq s1.toList; let subseqB := allSubseq s2.toList; let commonSubseq := subseqA.filter (fun l => subseqB.contains l); String.mk (commonSubseq.foldl (fun best l => if best.length < l.length then l else best) []))`
  - helper lemma `lcs_str_spec`: `∀ (L : List (List Char)), [] ∈ L → L.contains (String.mk (L.foldl (fun best l => if best.length < l.length then l else best) [])).toList = true ∧ L.all (fun l => decide (l.length ≤ (String.mk (L.foldl (fun best l => if best.length < l.length then l else best) [])).length)) = true`
  - helper lemma `lcs_str_ok`: `∀ (s1 s2 : String) (h : longestCommonSubsequence_precond s1 s2), longestCommonSubsequence_postcond s1 s2 (let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse; let subseqA := allSubseq s1.toList; let subseqB := allSubseq s2.toList; let commonSubseq := subseqA.filter (fun l => subseqB.contains l); String.mk (commonSubseq.foldl (fun best l => if best.length < l.length then l else best) [])) h`
