# Derivation of verina_advanced_64

kind: **restate**

- **term**: `lst.filter (fun x => decide (x ≠ target))`
  - helper lemma `rm64`: `∀ (lst : List Nat) (target : Nat) (h : removeElement_precond lst target), removeElement_postcond lst target (lst.filter (fun x => decide (x ≠ target))) h`
