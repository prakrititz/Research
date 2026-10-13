# Derivation of he_099_closest_integer

kind: **restate**

- **term**: `if parseDec value ≥ 0 then ⌊parseDec value + 1 / 2⌋ else -⌊-parseDec value + 1 / 2⌋`
  - helper lemma `round_away_ok`: `∀ (q : ℚ), |q - (((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)| < 1 / 2 ∨ (|q - (((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)| = 1 / 2 ∧ |q| < |(((if q ≥ 0 then ⌊q + 1 / 2⌋ else -⌊-q + 1 / 2⌋ : Int)) : ℚ)|)`
