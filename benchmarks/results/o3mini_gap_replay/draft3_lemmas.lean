-- the `k` largest elements in ascending order (he_120: `(arr.mergeSort (· ≥ ·)).take k |>.reverse`)
theorem reverse_isPerm {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.reverse.isPerm l = true := by
  rw [List.isPerm_iff]; exact List.reverse_perm l
theorem sorted_reverse_of_ge (l : List Int) (h : l.Pairwise (· ≥ ·)) :
    ∀ i, i < l.reverse.length - 1 → l.reverse[i]! ≤ l.reverse[i + 1]! := by
  intro i hi
  have hp : l.reverse.Pairwise (· ≤ ·) := List.pairwise_reverse.mpr h
  have hl : i + 1 < l.reverse.length := by omega
  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hl]
  exact List.pairwise_iff_getElem.mp hp i (i + 1) (by omega) hl (by omega)
theorem sorted_reverse_take_mergeSort_ge (arr : List Int) (k : Nat) :
    ∀ i, i < (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse.length - 1 →
      (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse[i]! ≤
        (List.take k (arr.mergeSort fun a b => decide (a ≥ b))).reverse[i + 1]! :=
  sorted_reverse_of_ge _ (List.Pairwise.take (pairwise_mergeSort_ge_int arr))

-- a palindrome by index (verina_basic_67: `x.reverse == x` against `∀ i < x.length, x[i]! = x[x.length - i - 1]!`)
theorem reverse_eq_self_iff_idx {α : Type} [Inhabited α] (l : List α) :
    l.reverse = l ↔ ∀ i, i < l.length → l[i]! = l[l.length - i - 1]! := by
  constructor
  · intro h i hi
    have hi' : l.length - i - 1 < l.length := by omega
    rw [getElem!_pos l i hi, getElem!_pos l _ hi']
    have e := congrArg (fun m => m[i]?) h
    simp only [List.getElem?_reverse hi, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : l.length - 1 - i < l.length)] at e
    have : l.length - 1 - i = l.length - i - 1 := by omega
    simp only [this, Option.some.injEq] at e
    exact e.symm
  · intro h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi' : l.length - i - 1 < l.length := by omega
    have := h i h2
    rw [getElem!_pos l i h2, getElem!_pos l _ hi'] at this
    rw [List.getElem_reverse, this]
    congr 1; omega

-- the same with `==` (a Bool result: `result ↔ ...`) and in `simp`'s form of `l[j]!` (`l[j]?.getD default`)
theorem reverse_beq_self_iff_idx {α : Type} [Inhabited α] [BEq α] [LawfulBEq α] (l : List α) :
    (l.reverse == l) = true ↔ ∀ i, i < l.length → l[i]! = l[l.length - i - 1]! := by
  rw [beq_iff_eq]; exact reverse_eq_self_iff_idx l
theorem reverse_eq_self_iff_idx' {α : Type} [Inhabited α] (l : List α) :
    l.reverse = l ↔ ∀ i (h : i < l.length), l[i] = l[l.length - i - 1]?.getD default := by
  rw [reverse_eq_self_iff_idx]
  refine forall_congr' fun i => ⟨fun h hi => ?_, fun h hi => ?_⟩ <;> have hj : l.length - i - 1 < l.length := by omega
  · have := h hi
    rw [getElem!_pos l i hi, getElem!_pos l _ hj] at this
    rw [List.getElem?_eq_getElem hj]; exact this
  · rw [getElem!_pos l i hi, getElem!_pos l _ hj, h hi, List.getElem?_eq_getElem hj]; rfl

-- sorted by a key, ties by value (he_116: `decide (ones a < ones b) || (ones a == ones b && a ≤ b)`); `grind +suggestions`
-- found this only while the library was small enough for its premise selection
theorem mergeSort_key_then_le (key : Int → Nat) (l : List Int) :
    ∀ i, i < (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b)))).length - 1 →
      key (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i]! <
          key (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i + 1]! ∨
        (key (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i]! =
            key (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i + 1]! ∧
          (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i]! ≤
            (l.mergeSort (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b))))[i + 1]!) := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (key a < key b) || (key a == key b && decide (a ≤ b)))
    (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) i hi
  simpa using this
