namespace Refine
theorem length_filter_range_succ (p : Nat → Bool) (i : Nat) :
    ((List.range (i + 1)).filter p).length = ((List.range i).filter p).length + (if p i = true then 1 else 0) := by
  rw [List.range_succ, List.filter_append]
  by_cases h : p i = true <;> simp [h]
theorem count_take_succ {α : Type} [BEq α] [Inhabited α] (l : List α) (x : α) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + (if l[i]! == x then 1 else 0) := by
  rw [take_succ_bang l i h, List.count_append]
  by_cases hx : (l[i]! == x) = true <;> simp [List.count_singleton, hx]
theorem countP_take_succ {α : Type} [Inhabited α] (l : List α) (p : α → Bool) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).countP p = (l.take i).countP p + (if p l[i]! then 1 else 0) := by
  rw [take_succ_bang l i h, List.countP_append]
  by_cases hp : p l[i]! = true <;> simp [hp]
end Refine
