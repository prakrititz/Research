# Derivation of verina_advanced_20

kind: **restate**

- **term**: `(n % 8 == 0) || (List.range (n.natAbs + 1)).any (fun i => n.natAbs / (10 ^ i) % 10 == 8)`
  - helper lemma `digit8_iff`: `∀ (absN : Nat), (∃ i : Nat, absN / (10 ^ i) % 10 = 8) ↔ (List.range (absN + 1)).any (fun i => decide (absN / (10 ^ i) % 10 = 8)) = true`
  - helper lemma `eight_ok`: `∀ (n : Int) (h : isItEight_precond n), isItEight_postcond n ((n % 8 == 0) || (List.range (n.natAbs + 1)).any (fun i => n.natAbs / (10 ^ i) % 10 == 8)) h`
