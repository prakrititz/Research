# Derivation of he_155_even_odd_count

kind: **loop**

- **bind** `ds : List Char` with property `ds = (toString num.natAbs).toList`
  - _value_:
    - **term**: `(toString num.natAbs).toList`
  - _continuation_:
    - **loop** over state (i : Nat, e : Nat, o : Nat), start (0, 0, 0)
      - invariant: `i ≤ ds.length ∧ e = ((ds.take i).filter (fun c => (c.toNat - 48) % 2 = 0)).length ∧ o = ((ds.take i).filter (fun c => (c.toNat - 48) % 2 = 1)).length`
      - guard: `i < ds.length`
      - variant: `ds.length - i`
      - result: `(e, o)`
      - **term**: `(i + 1, if (ds[i]!.toNat - 48) % 2 = 0 then e + 1 else e, if (ds[i]!.toNat - 48) % 2 = 1 then o + 1 else o)`
