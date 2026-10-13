# Derivation of verina_advanced_36

kind: **restate**

- **term**: `(xs.find? (fun x => decide (xs.count x > xs.length / 2))).getD 0`
  - helper lemma `maj36`: `∀ (xs : List Nat) (h : majorityElement_precond xs), majorityElement_postcond xs ((xs.find? (fun x => decide (xs.count x > xs.length / 2))).getD 0) h`
