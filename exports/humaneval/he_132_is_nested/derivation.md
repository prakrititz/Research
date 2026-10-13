# Derivation of he_132_is_nested

kind: **restate**

- **term**: `decide (∃ i, i < string.length ∧ ∃ len, len ≤ string.length - i ∧ 4 ≤ len ∧ isBalancedSq ((string.toList.drop i).take len) ∧ ∀ k, k < len → 0 < k → ¬ isBalancedSq (((string.toList.drop i).take len).take k))`
