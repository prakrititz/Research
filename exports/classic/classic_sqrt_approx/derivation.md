# Derivation of classic_sqrt_approx

kind: **loop**

- **loop** over state (k : Nat), start (0)
  - invariant: `((k : ℚ) * e) * ((k : ℚ) * e) ≤ N`
  - guard: `(((k : ℚ) + 1) * e) * (((k : ℚ) + 1) * e) ≤ N`
  - variant: `⌊(N + 1) / e⌋₊ + 1 - k`
  - result: `(k : ℚ) * e`
  - helper lemma `floor_bound`: `∀ (N e : ℚ) (k : ℕ), 0 ≤ N → 0 < e → ((k + 1 : ℚ) * e) * ((k + 1 : ℚ) * e) ≤ N → ⌊(N + 1) / e⌋₊ + 1 - (k + 1) < ⌊(N + 1) / e⌋₊ + 1 - k`
  - **term**: `k + 1`
