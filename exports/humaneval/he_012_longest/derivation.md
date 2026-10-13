# Derivation of he_012_longest

kind: **loop**

- **cases** on `strings = []`
  - _then_:
    - **term**: `none`
  - _else_:
    - **bind** `b : Nat` with property `b < strings.length ∧ (∀ j, j < strings.length → strings[j]!.length ≤ strings[b]!.length) ∧ ∀ j, j < b → strings[j]!.length < strings[b]!.length`
      - helper lemma `longest_exit`: `∀ (strings : List String) (b : Nat), (b < strings.length ∧ (∀ j, j < strings.length → strings[j]!.length ≤ strings[b]!.length) ∧ ∀ j, j < b → strings[j]!.length < strings[b]!.length) → ∃ i, i < strings.length ∧ strings[i]! = strings[b]! ∧ (∀ t ∈ strings, t.length ≤ strings[b]!.length) ∧ ∀ j, j < i → strings[j]!.length < strings[b]!.length`
      - _value_:
        - **loop** over state (k : Nat, b : Nat), start (1, 0)
          - invariant: `1 ≤ k ∧ k ≤ strings.length ∧ b < k ∧ (∀ j, j < k → strings[j]!.length ≤ strings[b]!.length) ∧ ∀ j, j < b → strings[j]!.length < strings[b]!.length`
          - guard: `k < strings.length`
          - variant: `strings.length - k`
          - result: `b`
          - **term**: `(k + 1, if strings[k]!.length > strings[b]!.length then k else b)`
      - _continuation_:
        - **term**: `some strings[b]!`
