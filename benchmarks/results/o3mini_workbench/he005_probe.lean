example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros k hk
  split_ifs with h0
  · omega
  · rw [Refine.getElem_bang_append]
    obtain ⟨_, hlen, _, hd⟩ := h1i
    rw [if_neg h0] at hlen
    split_ifs with h2
    · exact hd k (by omega)
    · have : 2 * k + 1 - acc.length = 0 := by omega
      rw [this]; rfl

-- the same, by a general recipe: intros, split the ifs, rewrite appends, split again, close by the hypotheses / omega
example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros
  split_ifs <;> simp only [Refine.getElem_bang_append] at * <;> split_ifs <;> simp_all <;> grind
