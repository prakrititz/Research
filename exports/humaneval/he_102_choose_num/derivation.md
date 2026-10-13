# Derivation of he_102_choose_num

kind: **restate**

- **cases** on `y < x`
  - _then_:
    - **term**: `-1`
  - _else_:
    - **cases** on `y % 2 = 0`
      - _then_:
        - **term**: `y`
      - _else_:
        - **cases** on `x ≤ y - 1`
          - _then_:
            - **term**: `y - 1`
          - _else_:
            - **term**: `-1`
