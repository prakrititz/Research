# Derivation of he_020_find_closest_elements

kind: **loop**

- **loop** over state (j : Nat, lo : ℚ, hi : ℚ), start (2, min numbers[0]! numbers[1]!, max numbers[0]! numbers[1]!)
  - invariant: `(lo ≤ hi ∧ (∃ b, b < j ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j ∧ j ≤ numbers.length`
  - guard: `j < numbers.length`
  - variant: `numbers.length - j`
  - result: `(lo, hi)`
  - helper lemma `maxmin_abs`: `∀ (x y : ℚ), max x y - min x y = |x - y|`
  - helper lemma `closest_yes`: `∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), i < j → j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → |numbers[i]! - numbers[j]!| < hi - lo → (((min numbers[i]! numbers[j]!) ≤ (max numbers[i]! numbers[j]!) ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ (((min numbers[i]! numbers[j]!) = numbers[a]! ∧ (max numbers[i]! numbers[j]!) = numbers[b]!) ∨ ((min numbers[i]! numbers[j]!) = numbers[b]! ∧ (max numbers[i]! numbers[j]!) = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → (max numbers[i]! numbers[j]!) - (min numbers[i]! numbers[j]!) ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < (i + 1) → (max numbers[i]! numbers[j]!) - (min numbers[i]! numbers[j]!) ≤ |numbers[a]! - numbers[j]!|)) ∧ i + 1 ≤ j)`
  - helper lemma `closest_no`: `∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), i < j → j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → ¬ |numbers[i]! - numbers[j]!| < hi - lo → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < (i + 1) → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i + 1 ≤ j)`
  - helper lemma `closest_inner_init`: `∀ (numbers : List ℚ) (j : Nat) (lo hi : ℚ), ((lo ≤ hi ∧ (∃ b, b < j ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j ∧ j ≤ numbers.length) → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < 0 → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ 0 ≤ j)`
  - helper lemma `closest_outer`: `∀ (numbers : List ℚ) (j : Nat) (lo hi : ℚ), j < numbers.length → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ j ≤ j) → 2 ≤ j → ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < (j + 1) → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ j + 1 ∧ j + 1 ≤ numbers.length)`
  - helper lemma `closest_init`: `∀ (numbers : List ℚ), numbers.length ≥ 2 → (((min numbers[0]! numbers[1]!) ≤ (max numbers[0]! numbers[1]!) ∧ (∃ b, b < 2 ∧ ∃ a, a < b ∧ (((min numbers[0]! numbers[1]!) = numbers[a]! ∧ (max numbers[0]! numbers[1]!) = numbers[b]!) ∨ ((min numbers[0]! numbers[1]!) = numbers[b]! ∧ (max numbers[0]! numbers[1]!) = numbers[a]!))) ∧ (∀ b, b < 2 → ∀ a, a < b → (max numbers[0]! numbers[1]!) - (min numbers[0]! numbers[1]!) ≤ |numbers[a]! - numbers[b]!|)) ∧ 2 ≤ 2 ∧ 2 ≤ numbers.length)`
  - helper lemma `closest_inner_exit`: `∀ (numbers : List ℚ) (i j : Nat) (lo hi : ℚ), ((lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi - lo ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j) → ¬ i < j → (lo ≤ hi ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo = numbers[a]! ∧ hi = numbers[b]!) ∨ (lo = numbers[b]! ∧ hi = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi - lo ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → hi - lo ≤ |numbers[a]! - numbers[j]!|))`
  - **bind** `p : ℚ × ℚ` with property `(p.1 ≤ p.2 ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((p.1 = numbers[a]! ∧ p.2 = numbers[b]!) ∨ (p.1 = numbers[b]! ∧ p.2 = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → p.2 - p.1 ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < j → p.2 - p.1 ≤ |numbers[a]! - numbers[j]!|))`
    - _value_:
      - **loop** over state (i : Nat, lo2 : ℚ, hi2 : ℚ), start (0, lo, hi)
        - invariant: `(lo2 ≤ hi2 ∧ (∃ b, b < (j + 1) ∧ ∃ a, a < b ∧ ((lo2 = numbers[a]! ∧ hi2 = numbers[b]!) ∨ (lo2 = numbers[b]! ∧ hi2 = numbers[a]!))) ∧ (∀ b, b < j → ∀ a, a < b → hi2 - lo2 ≤ |numbers[a]! - numbers[b]!|) ∧ (∀ a, a < i → hi2 - lo2 ≤ |numbers[a]! - numbers[j]!|)) ∧ i ≤ j`
        - guard: `i < j`
        - variant: `j - i`
        - result: `(lo2, hi2)`
        - **cases** on `|numbers[i]! - numbers[j]!| < hi2 - lo2`
          - _then_:
            - **term**: `(i + 1, min numbers[i]! numbers[j]!, max numbers[i]! numbers[j]!)`
          - _else_:
            - **term**: `(i + 1, lo2, hi2)`
    - _continuation_:
      - **term**: `(j + 1, p.1, p.2)`
