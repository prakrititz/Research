# Derivation of he_071_triangle_area

kind: **restate**

- **cases** on `a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a`
  - helper lemma `round_sqrt_ok`: `∀ (A : ℚ), 0 ≤ A → ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 ≥ 0 ∧ (((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100) * 100).den = 1 ∧ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 < 1 / 200 ∨ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 - 1 / 200) ^ 2 ≤ A) ∧ A ≤ ((((Nat.sqrt ⌊40000 * A⌋₊ + 1) / 2 : Nat) : ℚ) / 100 + 1 / 200) ^ 2)`
  - helper lemma `area2_nonneg`: `∀ (a b c : ℚ), a > 0 → b > 0 → c > 0 → ¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → 0 ≤ area2 a b c`
  - helper lemma `tri_no`: `∀ (a b c : ℚ), a > 0 → b > 0 → c > 0 → ¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → ((a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a → ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100) = -1) ∧ (¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) → ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 ≥ 0 ∧ (((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100) * 100).den = 1 ∧ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 < 1 / 200 ∨ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 - 1 / 200) ^ 2 ≤ area2 a b c) ∧ area2 a b c ≤ ((((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100 + 1 / 200) ^ 2)))`
  - _then_:
    - **term**: `-1`
  - _else_:
    - **term**: `(((Nat.sqrt ⌊40000 * area2 a b c⌋₊ + 1) / 2 : Nat) : ℚ) / 100`
