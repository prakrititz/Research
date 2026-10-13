# Derivation of verina_basic_35

kind: **restate**

- **term**: `Array.mk (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0))`
  - helper lemma `moveZeroes_ok`: `∀ (arr : Array Int) (h : MoveZeroesToEnd_precond arr), MoveZeroesToEnd_postcond arr (Array.mk (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0))) h`
