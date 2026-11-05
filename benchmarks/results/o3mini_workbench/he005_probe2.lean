-- R1
example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros; split_ifs <;> (try simp only [Refine.getElem_bang_append] at *) <;> (try split_ifs) <;> (try simp_all) <;> grind

-- R2
example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros; split_ifs <;> (try simp only [Refine.getElem_bang_append] at *) <;> (try split_ifs) <;> (try simp_all) <;> omega

-- R3
example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros; split_ifs <;> (try rw [Refine.getElem_bang_append]) <;> (try split_ifs) <;> (try simp_all) <;> (try grind)
