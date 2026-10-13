# Derivation of he_162_string_to_md5

kind: **restate**

- **cases** on `text = ""`
  - _then_:
    - **term**: `none`
  - _else_:
    - **term**: `some (md5Hex text)`
