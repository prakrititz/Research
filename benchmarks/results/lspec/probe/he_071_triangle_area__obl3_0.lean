/- term: the value satisfies the postcondition under the hypotheses
UNPROVED: no tactic of the cascade closes this

unsolved:
case right
a b c : ℚ
h_precond : triangleArea71_precond a b c
h1 : ¬(a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a)
⊢ ¬(a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) →
    ↑((⌊40000 * area2 a b c⌋₊.sqrt + 1) / 2) / 100 ≥ 0 ∧
      (↑((⌊40000 * area2 a b c⌋₊.sqrt + 1) / 2) / 100 * 100).den = 1 ∧
        (↑((⌊40000 * area2 a b c⌋₊.sqrt + 1) / 2) / 100 < 1 / 200 ∨
            (↑((⌊40000 * area2 a b c⌋₊.sqrt + 1) / 2) / 100 - 1 / 200) ^ 2 ≤ area2 a b c) ∧
          area2 a b c ≤ (↑((⌊40000 * area2 a b c⌋₊.sqrt + 1) / 2) / 100 + 1 / 200) ^ 2
-/
theorem probe (a : ℚ) (b : ℚ) (c : ℚ) (h_precond : triangleArea71_precond a b c) (h1 : ¬ (((a + b) ≤ c) ∨ (((a + c) ≤ b) ∨ ((b + c) ≤ a)))) :
    triangleArea71_postcond a b c ((((((Nat.sqrt ⌊40000 * (area2 a b c)⌋₊) + 1) / 2 : Nat) : Rat)) / 100) h_precond := by
  sorry
