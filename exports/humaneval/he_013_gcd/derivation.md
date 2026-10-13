# Derivation of he_013_gcd

kind: **restate**

- **term**: `Nat.gcd a b`
  - helper lemma `gcd_ok`: `∀ (a b : Nat), a > 0 → b > 0 → (Nat.gcd a b > 0 ∧ a % Nat.gcd a b = 0 ∧ b % Nat.gcd a b = 0 ∧ ∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ Nat.gcd a b)`
