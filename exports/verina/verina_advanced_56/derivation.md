# Derivation of verina_advanced_56

kind: **restate**

- **term**: `(xs.filter (fun x => decide (x ≠ 0)) ++ xs.filter (fun x => decide (x = 0)))`
  - helper lemma `isSub_append`: `∀ (F Z : List Int), isSubsequence F (F ++ Z) = true`
  - helper lemma `countVal_eq`: `∀ (v : Int) (l : List Int), countVal v l = l.count v`
  - helper lemma `move56`: `∀ (xs : List Int) (h : moveZeroes_precond xs), moveZeroes_postcond xs (xs.filter (fun x => decide (x ≠ 0)) ++ xs.filter (fun x => decide (x = 0))) h`
