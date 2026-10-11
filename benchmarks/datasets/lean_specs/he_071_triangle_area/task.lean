-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
def area2 (a b c : ℚ) : ℚ :=
  let p := (a + b + c) / 2
  p * (p - a) * (p - b) * (p - c)
-- !benchmark @end precond_aux

@[reducible, simp]
def triangleArea71_precond (a : ℚ) (b : ℚ) (c : ℚ) : Prop :=
  -- !benchmark @start precond
  a > 0 ∧ b > 0 ∧ c > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def triangleArea71 (a : ℚ) (b : ℚ) (c : ℚ) (h_precond : triangleArea71_precond (a) (b) (c)) : ℚ :=
  -- !benchmark @start code
  if a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a then -1 else
    let q := area2 a b c * 10000
    let m := Nat.sqrt (q.num.toNat / q.den)
    let r := if ((m : ℚ) + 1 / 2) ^ 2 ≤ q then m + 1 else m
    (r : ℚ) / 100
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def triangleArea71_postcond (a : ℚ) (b : ℚ) (c : ℚ) (result: ℚ) (h_precond : triangleArea71_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a → result = -1) ∧
    (¬ (a + b ≤ c ∨ a + c ≤ b ∨ b + c ≤ a) →
      result ≥ 0 ∧ (result * 100).den = 1 ∧ (result < 1 / 200 ∨ (result - 1 / 200) ^ 2 ≤ area2 a b c) ∧
        area2 a b c ≤ (result + 1 / 200) ^ 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem triangleArea71_spec_satisfied (a : ℚ) (b : ℚ) (c : ℚ) (h_precond : triangleArea71_precond (a) (b) (c)) :
    triangleArea71_postcond (a) (b) (c) (triangleArea71 (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof
