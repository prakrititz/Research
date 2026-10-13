# Derivation of verina_basic_66

kind: **restate**

- **term**: `decide (x % 2 = 0)`
  - helper lemma `even_ok`: `∀ (x : Int), (decide (x % 2 = 0) = true ↔ ∃ k : Int, x = 2 * k)`
