# Derivation of he_119_match_parens

kind: **restate**

- **cases** on `isBalanced (lst[0]!.toList ++ lst[1]!.toList) ∨ isBalanced (lst[1]!.toList ++ lst[0]!.toList)`
  - _then_:
    - **term**: `"Yes"`
  - _else_:
    - **term**: `"No"`
