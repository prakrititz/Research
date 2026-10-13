# Derivation of verina_basic_39

kind: **restate**

- **cases** on `l.length = 0`
  - helper lemma `rotate_ok`: `∀ (l : List Int) (n : Nat) (h : rotateRight_precond l n), l.length ≠ 0 → rotateRight_postcond l n ((List.range l.length).map (fun i : Nat => l.getD (Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % Int.ofNat l.length)) (l.headD 0))) h`
  - _then_:
    - **term**: `l`
  - _else_:
    - **term**: `(List.range l.length).map (fun i : Nat => l.getD (Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % Int.ofNat l.length)) (l.headD 0))`
