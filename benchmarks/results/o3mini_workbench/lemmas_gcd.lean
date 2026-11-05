namespace Refine
theorem le_gcd_of_mod_left (a b d : Nat) (ha : 0 < a) (hda : a % d = 0) (hdb : b % d = 0) : d ≤ Nat.gcd a b :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hda) (Nat.dvd_of_mod_eq_zero hdb))
theorem le_gcd_of_mod_right (a b d : Nat) (hb : 0 < b) (hda : a % d = 0) (hdb : b % d = 0) : d ≤ Nat.gcd a b :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_right a hb) (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hda) (Nat.dvd_of_mod_eq_zero hdb))
end Refine
example (a b : Nat) (h : a > 0 ∧ b > 0) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  intros d _ _ hda hdb
  exact Refine.le_gcd_of_mod_left a b d h.1 hda hdb
example (a b : Nat) (h : a > 0 ∧ b > 0) : ∀ d < a + b + 1, d > 0 → a % d = 0 → b % d = 0 → d ≤ a.gcd b := by
  (try intros); (repeat' apply And.intro) <;> (try intros) <;> first | omega | solve_by_elim (maxDepth := 4) [Refine.le_gcd_of_mod_left, Refine.le_gcd_of_mod_right, And.left, And.right]
