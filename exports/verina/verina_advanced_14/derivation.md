# Derivation of verina_advanced_14

kind: **restate**

- **term**: `(List.range (n + 1)).any (fun m => decide (n = 4 ^ m))`
  - helper lemma `pow4_iff`: `∀ (n : Nat), (∃ m : Nat, n = 4 ^ m) ↔ (List.range (n + 1)).any (fun m => decide (n = 4 ^ m)) = true`
  - helper lemma `pow4_ok`: `∀ (n : Nat) (h : ifPowerOfFour_precond n), ifPowerOfFour_postcond n ((List.range (n + 1)).any (fun m => decide (n = 4 ^ m))) h`
