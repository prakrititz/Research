namespace Refine
theorem getElem_bang_cons {α : Type} [Inhabited α] (x : α) (xs : List α) (j : Nat) :
    (x :: xs)[j]! = if j = 0 then x else xs[j - 1]! := by
  cases j with
  | zero => simp
  | succ n => simp
theorem getElem_bang_nil {α : Type} [Inhabited α] (j : Nat) : ([] : List α)[j]! = default := by simp
end Refine

example (numbers : List Int) (delimeter : Int) (i : Nat) (acc : List Int)
    (h1i : i ≤ numbers.length ∧ (acc.length = if i = 0 then 0 else 2 * i - 1) ∧
      (∀ k < i, acc[2 * k]! = numbers[k]!) ∧ ∀ (k : ℕ), k + 1 < i → acc[2 * k + 1]! = delimeter)
    (h1g : i < numbers.length) :
    ∀ (k : ℕ), k + 1 < i + 1 → (if i = 0 then [numbers[0]!] else acc ++ [delimeter, numbers[i]!])[2 * k + 1]! = delimeter := by
  intros; split_ifs <;> (try simp only [Refine.getElem_bang_append, Refine.getElem_bang_cons, Refine.getElem_bang_nil] at *) <;> (try split_ifs) <;> (first | omega | (apply_assumption <;> omega) | grind)
