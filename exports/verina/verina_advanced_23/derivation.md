# Derivation of verina_advanced_23

kind: **restate**

- **term**: `(List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0))`
  - helper lemma `pow2_iff`: `∀ (n : Int), (∃ x : Nat, _root_.pow 2 x = n ∧ n > 0) ↔ (List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0)) = true`
  - helper lemma `pow2_ok`: `∀ (n : Int) (h : isPowerOfTwo_precond n), isPowerOfTwo_postcond n ((List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0))) h`
