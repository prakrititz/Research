# Derivation of verina_basic_4

kind: **restate**

- **term**: `arr[k - 1]!`
  - helper lemma `kth4`: `∀ (arr : Array Int) (k : Nat) (h : kthElement_precond arr k), kthElement_postcond arr k (arr[k - 1]!) h`
