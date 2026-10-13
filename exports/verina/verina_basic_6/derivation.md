# Derivation of verina_basic_6

kind: **restate**

- **cases** on `a ≤ b ∧ a ≤ c`
  - _then_:
    - **term**: `a`
  - _else_:
    - **cases** on `b ≤ a ∧ b ≤ c`
      - _then_:
        - **term**: `b`
      - _else_:
        - **term**: `c`
