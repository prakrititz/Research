# Derivation of he_118_get_closest_vowel

kind: **loop**

- **bind** `last : Option Nat` with property `(last = none ∧ ∀ i, i < word.toList.length → ¬ goodAt word.toList i) ∨ (∃ b, last = some b ∧ b < word.toList.length ∧ goodAt word.toList b ∧ ∀ j, j < word.toList.length → b < j → ¬ goodAt word.toList j)`
  - helper lemma `vowel_step`: `∀ (w : List Char) (i : Nat) (b : Option Nat), (i ≤ w.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt w j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt w c ∧ ∀ j, j < i → c < j → ¬ goodAt w j))) → i < w.length → (i + 1 ≤ w.length ∧ (((if goodAt w i then some i else b) = none ∧ ∀ j, j < i + 1 → ¬ goodAt w j) ∨ (∃ c, (if goodAt w i then some i else b) = some c ∧ c < i + 1 ∧ goodAt w c ∧ ∀ j, j < i + 1 → c < j → ¬ goodAt w j)))`
  - helper lemma `vowel_none`: `∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → last = none → (("" = "" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ ("" ≠ "" → ∃ i, i < w.length ∧ goodAt w i ∧ "" = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))`
  - helper lemma `vowel_some`: `∀ (w : List Char) (last : Option Nat), ((last = none ∧ ∀ i, i < w.length → ¬ goodAt w i) ∨ (∃ b, last = some b ∧ b < w.length ∧ goodAt w b ∧ ∀ j, j < w.length → b < j → ¬ goodAt w j)) → ¬ last = none → ((String.singleton w[last.getD 0]! = "" ↔ ∀ i, i < w.length → ¬ goodAt w i) ∧ (String.singleton w[last.getD 0]! ≠ "" → ∃ i, i < w.length ∧ goodAt w i ∧ String.singleton w[last.getD 0]! = String.singleton w[i]! ∧ ∀ j, j < w.length → i < j → ¬ goodAt w j))`
  - _value_:
    - **loop** over state (i : Nat, b : Option Nat), start (0, none)
      - invariant: `i ≤ word.toList.length ∧ ((b = none ∧ ∀ j, j < i → ¬ goodAt word.toList j) ∨ (∃ c, b = some c ∧ c < i ∧ goodAt word.toList c ∧ ∀ j, j < i → c < j → ¬ goodAt word.toList j))`
      - guard: `i < word.toList.length`
      - variant: `word.toList.length - i`
      - result: `b`
      - **term**: `(i + 1, if goodAt word.toList i then some i else b)`
  - _continuation_:
    - **cases** on `last = none`
      - _then_:
        - **term**: `""`
      - _else_:
        - **term**: `String.singleton word.toList[last.getD 0]!`
