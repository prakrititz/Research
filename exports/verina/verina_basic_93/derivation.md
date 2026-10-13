# Derivation of verina_basic_93

kind: **restate**

- **term**: `(Y, X)`
  - helper lemma `swapbitvectors_ok`: `∀ (X Y : UInt8) (h : SwapBitvectors_precond X Y), SwapBitvectors_postcond X Y (Y, X) h`
