# Derivation of verina_advanced_5

kind: **restate**

- **term**: `(if listToNat l1 + listToNat l2 = 0 then [0] else Nat.digits 10 (listToNat l1 + listToNat l2))`
  - helper lemma `l2n`: `∀ (l : List Nat), listToNat l = Nat.ofDigits 10 l`
  - helper lemma `gl_cc`: `∀ (a b : Nat) (t : List Nat), (a :: b :: t).getLast! = (b :: t).getLast!`
  - helper lemma `last_pos`: `∀ (l : List Nat), l ≠ [] → l.getLast! ≠ 0 → 0 < listToNat l`
  - helper lemma `digits_last`: `∀ (s : Nat), s ≠ 0 → (Nat.digits 10 s).getLast! ≠ 0`
  - helper lemma `add5`: `∀ (l1 l2 : List Nat) (h : addTwoNumbers_precond l1 l2), addTwoNumbers_postcond l1 l2 (if listToNat l1 + listToNat l2 = 0 then [0] else Nat.digits 10 (listToNat l1 + listToNat l2)) h`
