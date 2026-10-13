# Derivation of he_065_circular_shift

kind: **restate**

- **bind** `d : List Char` with property `d = (toString x).toList`
  - _value_:
    - **term**: `(toString x).toList`
  - _continuation_:
    - **term**: `String.mk (if shift > d.length then d.reverse else d.drop (d.length - shift % d.length) ++ d.take (d.length - shift % d.length))`
