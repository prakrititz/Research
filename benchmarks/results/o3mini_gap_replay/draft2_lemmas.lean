-- every element equal to the first: all pairs equal (verina_basic_41's exit `∀ j < a.size, a[j]! = a[0]!`)
theorem pairwise_eq_of_all_eq_head {α : Type} [Inhabited α] (l : List α) (h : ∀ k, k < l.length → l[k]! = l[0]!) :
    List.Pairwise (· = ·) l := by
  apply List.pairwise_of_forall_mem_list
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := (mem_iff_idx l x).mp hx
  obtain ⟨j, hj, rfl⟩ := (mem_iff_idx l y).mp hy
  rw [h i hi, h j hj]
theorem pairwise_eq_of_all_eq_head_arr {α : Type} [Inhabited α] (a : Array α) (h : ∀ k, k < a.size → a[k]! = a[0]!) :
    List.Pairwise (· = ·) a.toList := by
  apply List.pairwise_of_forall_mem_list
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := (mem_iff_idx a.toList x).mp hx
  obtain ⟨j, hj, rfl⟩ := (mem_iff_idx a.toList y).mp hy
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  rw [toList_getElem_bang a i hi', toList_getElem_bang a j hj', h i hi', h j hj']

-- the search for a square root went past it (verina_basic_48's exit: `∀ j < i, j * j ≠ n`, `¬ i * i ≤ n`)
theorem not_exists_sq_of_bounds (n i : Nat) (h1 : ∀ j, j < i → j * j ≠ n) (h2 : n < i * i) : ¬ ∃ k, k * k = n := by
  rintro ⟨k, hk⟩
  by_cases hki : k < i
  · exact h1 k hki hk
  · have : i * i ≤ k * k := Nat.mul_self_le_mul_self (by omega)
    omega
theorem exists_sq_iff_of_bounds (n r : Nat) (h1 : r * r ≤ n) (h2 : n < (r + 1) * (r + 1)) :
    (∃ i, i * i = n) ↔ r * r = n := by
  constructor
  · rintro ⟨i, hi⟩
    rcases lt_trichotomy i r with hlt | heq | hgt
    · exfalso; nlinarith
    · subst heq; exact hi
    · exfalso; nlinarith
  · intro h; exact ⟨r, h⟩

-- a sorted array: the prefix up to an element below `key` is below `key`, the suffix from one at least `key` is at least
-- `key` (verina_basic_51's binary search)
theorem sorted_take_succ_all_lt (a : Array Int) (key : Int) (m : Nat) (hm : m < a.size)
    (hs : List.Pairwise (· ≤ ·) a.toList) (h : a[m] < key) : ((a.take (m + 1)).all fun x => decide (x < key)) = true := by
  rw [arr_all_take_iff]
  intro k hk hks
  have := sorted_arr_le a hs k m (by omega) hm
  rw [getElem!_pos a m hm] at this
  simp only [decide_eq_true_eq]; omega
theorem sorted_drop_all_ge (a : Array Int) (key : Int) (m : Nat) (hm : m < a.size)
    (hs : List.Pairwise (· ≤ ·) a.toList) (h : key ≤ a[m]) : ((a.drop m).all fun x => decide (x ≥ key)) = true := by
  rw [arr_all_drop_iff]
  intro k hk hks
  have := sorted_arr_le a hs m k hk hks
  rw [getElem!_pos a m hm] at this
  simp only [decide_eq_true_eq]; omega

-- keeping the elements a test accepts by pushing them onto an array is `filter` (verina_basic_34)
theorem foldl_push_filter {α : Type} (p : α → Bool) (l : List α) (init : Array α) :
    (List.foldl (fun acc x => if p x = true then acc.push x else acc) init l).toList = init.toList ++ l.filter p := by
  induction l generalizing init with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.filter_cons]
    split <;> simp_all
theorem arr_foldl_push_filter {α : Type} (p : α → Bool) (a : Array α) :
    (Array.foldl (fun acc x => if p x = true then acc.push x else acc) #[] a).toList = a.toList.filter p := by
  rw [← Array.foldl_toList, foldl_push_filter]; simp
-- `filter` keeps the order of what it keeps
theorem idxOf_filter_le {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (l : List α) (x y : α) (hx : p x = true)
    (h : l.idxOf x ≤ l.idxOf y) : (l.filter p).idxOf x ≤ (l.filter p).idxOf y := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hax : a = x
    · subst hax; simp [List.filter_cons, hx, List.idxOf_cons]
    · by_cases hay : a = y
      · subst hay; simp [List.idxOf_cons, beq_iff_eq, hax] at h
      · have h' : t.idxOf x ≤ t.idxOf y := by simp [List.idxOf_cons, beq_iff_eq, hax, hay] at h; omega
        cases hpa : p a <;> simp [List.filter_cons, hpa, List.idxOf_cons, beq_iff_eq, hax, hay, ih h']

-- moving the copies of `a` to the end (verina_basic_35)
theorem idxOf_append_not_mem {α : Type} [BEq α] [LawfulBEq α] (a : α) (l₁ l₂ : List α) (h : a ∉ l₁) :
    (l₁ ++ l₂).idxOf a = l₁.length + l₂.idxOf a := by
  induction l₁ with
  | nil => simp
  | cons b t ih =>
    simp only [List.mem_cons, not_or] at h
    have hb : (b == a) = false := by simpa [beq_iff_eq] using Ne.symm h.1
    simp [List.idxOf_cons, hb, ih h.2]; omega
theorem idxOf_filter_ne_append {α : Type} [DecidableEq α] (a : α) (l : List α) :
    (l.filter (· ≠ a) ++ l.filter (· = a)).idxOf a = (l.filter (· ≠ a)).length := by
  rw [idxOf_append_not_mem _ _ _ (by simp)]
  cases h : l.filter (· = a) with
  | nil => simp
  | cons b t =>
    have hb : b = a := by
      have := (List.mem_filter.mp (h ▸ List.mem_cons_self : b ∈ l.filter (· = a))).2
      simpa using this
    subst hb; simp [List.idxOf_cons]
theorem filter_ne_append_filter_eq_perm {α : Type} [DecidableEq α] (a : α) (l : List α) :
    (l.filter (· ≠ a) ++ l.filter (· = a)).isPerm l = true := by
  rw [List.isPerm_iff]
  have := List.filter_append_perm (fun x => decide (x ≠ a)) l
  simpa using this

-- `c * b^m = b^x` and `b ∤ c`: `c = 1` (the exit of a loop dividing out `b`: verina_advanced_14, verina_advanced_23)
theorem eq_one_of_mul_pow_eq_pow (b c m x : Nat) (hb : 1 < b) (h : c * b ^ m = b ^ x) (hc : c % b ≠ 0) : c = 1 := by
  have hbm : 0 < b ^ m := Nat.pow_pos (by omega)
  rcases Nat.lt_or_ge x m with hx | hx
  · exfalso
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have h1 : b ^ x < b ^ m := Nat.pow_lt_pow_right hb hx
    have h2 : b ^ m ≤ c * b ^ m := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, x = m + k := ⟨x - m, by omega⟩
    rw [pow_add, mul_comm (b ^ m)] at h
    have hck : c = b ^ k := Nat.eq_of_mul_eq_mul_right hbm h
    cases k with
    | zero => simpa using hck
    | succ k => exfalso; apply hc; rw [hck, pow_succ]; simp
theorem pow_iff_of_factor (b n c : Nat) (hb : 1 < b) (h : ∃ m, n = c * b ^ m) (hc : c ≠ 1 → c % b ≠ 0) :
    c = 1 ↔ ∃ x, n = b ^ x := by
  obtain ⟨m, rfl⟩ := h
  constructor
  · rintro rfl; exact ⟨m, by simp⟩
  · rintro ⟨x, hx⟩
    by_contra hne
    exact hne (eq_one_of_mul_pow_eq_pow b c m x hb hx (hc hne))

-- the common divisors of `a` and `b` are the divisors of `g`: `g` is their greatest common divisor (he_013's Euclid exit)
theorem mod_left_of_common_divisors (a b g : Nat) (hg : g > 0) (h : ∀ d, d > 0 → (a % d = 0 ∧ b % d = 0 ↔ g % d = 0)) :
    a % g = 0 := ((h g hg).mpr (Nat.mod_self g)).1
theorem mod_right_of_common_divisors (a b g : Nat) (hg : g > 0) (h : ∀ d, d > 0 → (a % d = 0 ∧ b % d = 0 ↔ g % d = 0)) :
    b % g = 0 := ((h g hg).mpr (Nat.mod_self g)).2
theorem le_of_common_divisors (a b g : Nat) (P : Nat → Prop) (hg : g > 0)
    (h : ∀ d, d > 0 → (a % d = 0 ∧ b % d = 0 ↔ g % d = 0)) : ∀ d, P d → d > 0 → a % d = 0 → b % d = 0 → d ≤ g := by
  intro d _ hd ha hb
  exact Nat.le_of_dvd hg (Nat.dvd_of_mod_eq_zero ((h d hd).mp ⟨ha, hb⟩))
