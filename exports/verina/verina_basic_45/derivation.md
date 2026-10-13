# Derivation of verina_basic_45

kind: **restate**

- **term**: `match firstEvenOddIndices lst with | some (ei, oi) => lst[ei]! * lst[oi]! | none => 0`
  - helper lemma `findproduct_post`: `∀ (lst : List Int) (h : findProduct_precond lst), findProduct_postcond lst (match firstEvenOddIndices lst with | some (ei, oi) => lst[ei]! * lst[oi]! | none => 0) h`
