# Derivation of he_103_rounded_avg

kind: **restate**

- **cases** on `n > m`
  - helper lemma `toDigits2_binary`: `∀ (v : Nat), isBinary (Nat.toDigits 2 v) v`
  - helper lemma `toDigits2_ne_nil`: `∀ (v : Nat), Nat.toDigits 2 v ≠ []`
  - helper lemma `ob_ok`: `∀ (w : Nat), ((String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).length ≥ 3 ∧ (String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).toList.take 2 = ['0', 'b'] ∧ isBinary ((String.mk (['0', 'b'] ++ Nat.toDigits 2 w)).toList.drop 2) w)`
  - _then_:
    - **term**: `none`
  - _else_:
    - **term**: `some (String.mk (['0', 'b'] ++ Nat.toDigits 2 (roundedHalfEven (n + m))))`
