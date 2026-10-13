# Derivation of he_006_parse_nested_parens

kind: **loop**

- **bind** `groups : List String` with property `groups = (paren_string.splitOn " ").filter (fun g => g != "")`
  - _value_:
    - **term**: `(paren_string.splitOn " ").filter (fun g => g != "")`
  - _continuation_:
    - **loop** over state (i : Nat, acc : List Nat), start (0, [])
      - invariant: `i ≤ groups.length ∧ acc = (groups.take i).map (fun g => maxDepth g.toList)`
      - guard: `i < groups.length`
      - variant: `groups.length - i`
      - result: `acc`
      - **term**: `(i + 1, acc ++ [maxDepth groups[i]!.toList])`
