# Derivation of he_161_solve

kind: **restate**

- **cases** on `s.toList.any Char.isAlpha = true`
  - _then_:
    - **term**: `String.mk (s.toList.map swapCase)`
  - _else_:
    - **term**: `String.mk s.toList.reverse`
