# Derivation of verina_advanced_41

kind: **restate**

- **bind** `m : Int` with property `m ≥ a ∧ m ≥ b ∧ (m = a ∨ m = b)`
  - _value_:
    - **cases** on `a ≥ b`
      - _then_:
        - **term**: `a`
      - _else_:
        - **term**: `b`
  - _continuation_:
    - **cases** on `m ≥ c`
      - _then_:
        - **term**: `m`
      - _else_:
        - **term**: `c`
