# Derivation of verina_basic_27

kind: **restate**

- **term**: `(match (List.range s.toList.length).find? (fun i => decide (s.toList[i]! ∈ s.toList.take i)) with | none => none | some i => some s.toList[i]!)`
  - helper lemma `idxOf_le_of_getElem_c`: `∀ (s : List Char) (k : Nat) (a : Char), s[k]? = some a → s.idxOf a ≤ k`
  - helper lemma `nodup_of_no_rep`: `∀ (cs : List Char) (n : Nat), n ≤ cs.length → (∀ i, i < n → cs[i]! ∉ cs.take i) → List.Pairwise (· ≠ ·) (cs.take n)`
  - helper lemma `rep27`: `∀ (s : String) (h : findFirstRepeatedChar_precond s), findFirstRepeatedChar_postcond s (match (List.range s.toList.length).find? (fun i => decide (s.toList[i]! ∈ s.toList.take i)) with | none => none | some i => some s.toList[i]!) h`
