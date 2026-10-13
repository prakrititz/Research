# Derivation of he_158_find_max

kind: **loop**

- **cases** on `words = []`
  - _then_:
    - **term**: `""`
  - _else_:
    - **bind** `m : String` with property `m ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars m) ∧ ∀ w ∈ words, uniqChars w = uniqChars m → ¬ (w < m)`
      - _value_:
        - **loop** over state (k : Nat, b : Nat), start (1, 0)
          - invariant: `1 ≤ k ∧ k ≤ words.length ∧ b < k ∧ (∀ j, j < k → uniqChars words[j]! ≤ uniqChars words[b]!) ∧ ∀ j, j < k → uniqChars words[j]! = uniqChars words[b]! → ¬ (words[j]! < words[b]!)`
          - guard: `k < words.length`
          - variant: `words.length - k`
          - result: `words[b]!`
          - **term**: `(k + 1, if uniqChars words[k]! > uniqChars words[b]! ∨ (uniqChars words[k]! = uniqChars words[b]! ∧ words[k]! < words[b]!) then k else b)`
      - _continuation_:
        - **term**: `m`
