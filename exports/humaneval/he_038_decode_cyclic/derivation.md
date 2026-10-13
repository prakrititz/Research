# Derivation of he_038_decode_cyclic

kind: **restate**

- **term**: `String.mk (encodeGroups (encodeGroups s.toList))`
  - helper lemma `encode_three`: `∀ (l : List Char), encodeGroups (encodeGroups (encodeGroups l)) = l`
