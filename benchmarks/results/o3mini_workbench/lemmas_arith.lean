namespace Refine
theorem mod_gcd_left (a b : Nat) : a % Nat.gcd a b = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b)
theorem mod_gcd_right (a b : Nat) : b % Nat.gcd a b = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)
theorem mod_eq_zero_of_dvd' (a b : Nat) (h : a ∣ b) : b % a = 0 := Nat.mod_eq_zero_of_dvd h
theorem dvd_of_mod_eq_zero' (a b : Nat) (h : b % a = 0) : a ∣ b := Nat.dvd_of_mod_eq_zero h
theorem le_of_dvd_pos (a b : Nat) (hb : 0 < b) (h : a ∣ b) : a ≤ b := Nat.le_of_dvd hb h
theorem mergeSort_ge_nat (l : List Nat) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≥ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (l.mergeSort (fun a b => decide (a ≥ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this
end Refine
example (a b : Nat) : a % a.gcd b = 0 := by solve_by_elim [Refine.mod_gcd_left]
