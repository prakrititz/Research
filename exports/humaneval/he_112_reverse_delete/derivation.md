# Derivation of he_112_reverse_delete

kind: **restate**

- **bind** `t : List Char` with property `t = s.toList.filter (fun ch => !(c.toList.contains ch))`
  - _value_:
    - **term**: `s.toList.filter (fun ch => !(c.toList.contains ch))`
  - _continuation_:
    - **term**: `(String.mk t, decide (t = t.reverse))`
