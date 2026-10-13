import Mathlib

def area2 (a b c : ℚ) : ℚ :=
  let p := (a + b + c) / 2
  p * (p - a) * (p - b) * (p - c)

@[reducible, simp]
def triangleArea71_precond (a : ℚ) (b : ℚ) (c : ℚ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0

@[reducible, simp]
def triangleArea71_postcond (a : ℚ) (b : ℚ) (c : ℚ) (result: ℚ) (h_precond : triangleArea71_precond (a) (b) (c)) :=
  (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a → result = -1) ∧
    (¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) →
      result ≥ 0 ∧ (result * 100).den = 1 ∧ (result < 1 / 200 ∨ (result - 1 / 200) ^ 2 ≤ area2 a b c) ∧
        area2 a b c ≤ (result + 1 / 200) ^ 2)
