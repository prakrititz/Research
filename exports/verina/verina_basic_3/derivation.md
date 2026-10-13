# Derivation of verina_basic_3

kind: **restate**

- **term**: `decide (n % 11 = 0)`
  - helper lemma `div11_ok`: `∀ (n : Int), (decide (n % 11 = 0) = true → ∃ k : Int, n = 11 * k) ∧ (¬ decide (n % 11 = 0) = true → ∀ k : Int, ¬ n = 11 * k)`
