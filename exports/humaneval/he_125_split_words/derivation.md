# Derivation of he_125_split_words

kind: **restate**

- **bind** `hasWhite : Bool` with property `hasWhite = txt.toList.any (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')`
  - _value_:
    - **term**: `txt.toList.any (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')`
  - _continuation_:
    - **term**: `if hasWhite = true then Sum.inl (splitWhite txt) else if txt.toList.contains ',' then Sum.inl (txt.splitOn ",") else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 = 1)).length)`
