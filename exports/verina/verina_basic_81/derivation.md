# Derivation of verina_basic_81

kind: **restate**

- **cases** on `y = 0`
  - helper lemma `divmod_ok`: `∀ (x y : Nat), y ≠ 0 → (Int.ofNat (x / y) * Int.ofNat y + Int.ofNat (x % y) = Int.ofNat x ∧ (0 ≤ Int.ofNat (x % y) ∧ Int.ofNat (x % y) < Int.ofNat y) ∧ 0 ≤ Int.ofNat (x / y))`
  - _then_:
    - **term**: `(Int.ofNat x, 0)`
  - _else_:
    - **term**: `(Int.ofNat (x % y), Int.ofNat (x / y))`
