# Derivation of he_137_compare_one

kind: **restate**

- **cases** on `valQ a = valQ b`
  - _then_:
    - **term**: `none`
  - _else_:
    - **cases** on `valQ b < valQ a`
      - _then_:
        - **term**: `some a`
      - _else_:
        - **term**: `some b`
