import Mathlib


namespace Refine

theorem forall_mem_iff_idx {α : Type} [Inhabited α] (l : List α) (P : α → Prop) :
    (∀ x ∈ l, P x) ↔ ∀ k, k < l.length → P l[k]! := by
  constructor
  · intro h k hk
    have hmem : l[k]! ∈ l := by
      rw [getElem!_pos l k hk]; exact List.getElem_mem hk
    exact h _ hmem
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    have := h k hk
    rwa [getElem!_pos l k hk] at this

theorem exists_mem_iff_idx {α : Type} [Inhabited α] (l : List α) (P : α → Prop) :
    (∃ x ∈ l, P x) ↔ ∃ k, k < l.length ∧ P l[k]! := by
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨k, hk, by rwa [getElem!_pos l k hk]⟩
  · rintro ⟨k, hk, hp⟩
    exact ⟨l[k]!, by rw [getElem!_pos l k hk]; exact List.getElem_mem hk, hp⟩

theorem mem_iff_idx {α : Type} [Inhabited α] (l : List α) (x : α) :
    x ∈ l ↔ ∃ k, k < l.length ∧ l[k]! = x := by
  have := exists_mem_iff_idx l (fun y => y = x)
  simpa using this

theorem getElem_bang_mem {α : Type} [Inhabited α] (l : List α) (k : Nat) (h : k < l.length) : l[k]! ∈ l := by
  rw [getElem!_pos l k h]; exact List.getElem_mem h

theorem getElem_bang_mem_take {α : Type} [Inhabited α] (l : List α) (k n : Nat) (hk : k < n) (hl : k < l.length) :
    l[k]! ∈ l.take n := by
  have h1 : k < (l.take n).length := by simp; omega
  rw [getElem!_pos l k hl]
  have h2 : l[k] = (l.take n)[k] := by simp [List.getElem_take]
  rw [h2]; exact List.getElem_mem h1

theorem head_mem_take_one {α : Type} [Inhabited α] (l : List α) (h : l ≠ []) : l[0]! ∈ l.take 1 := by
  cases l with
  | nil => contradiction
  | cons x xs => simp

theorem string_length_mk (l : List Char) : (String.mk l).length = l.length := String.length_ofList

theorem string_toList_mk (l : List Char) : (String.mk l).toList = l := String.toList_ofList

theorem take_succ_bang {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]!] := by
  rw [List.take_succ_eq_append_getElem h, getElem!_pos l i h]

theorem filter_take_succ_bang {α : Type} [Inhabited α] (p : α → Bool) (l : List α) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).filter p = (l.take i).filter p ++ (if p l[i]! = true then [l[i]!] else []) := by
  rw [take_succ_bang l i h, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

theorem sorted_filter_range (n : Nat) (p : Nat → Bool) :
    ∀ i, i < ((List.range n).filter p).length - 1 → ((List.range n).filter p)[i]! < ((List.range n).filter p)[i + 1]! := by
  have hs : List.Pairwise (· < ·) ((List.range n).filter p) := (List.pairwise_lt_range).filter _
  intro i hi
  rw [List.pairwise_iff_getElem] at hs
  have hi' : i + 1 < ((List.range n).filter p).length := by omega
  have := hs i (i + 1) (by omega) hi' (by omega)
  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']
  exact this

theorem sum_take_succ_bang (l : List Int) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l[i]! := by
  rw [take_succ_bang l i h, List.sum_append]; simp

theorem head_bang_eq {α : Type} [Inhabited α] (l : List α) (h : l ≠ []) : l.head! = l[0]! := by
  cases l with
  | nil => contradiction
  | cons x xs => simp

theorem getElem_bang_append_lt {α : Type} [Inhabited α] (a b : List α) (k : Nat) (h : k < a.length) :
    (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k h, List.getElem_append_left h]

theorem getElem_bang_append_length {α : Type} [Inhabited α] (a : List α) (x : α) :
    (a ++ [x])[a.length]! = x := by
  rw [getElem!_pos (a ++ [x]) a.length (by simp)]; simp

theorem take_string_length (s : String) : s.toList.take s.length = s.toList := by
  have h : s.toList.length = s.length := rfl
  rw [← h]; exact List.take_length

theorem exists_le_succ (P : Nat → Prop) (i : Nat) :
    (∃ k, k ≤ i + 1 ∧ P k) ↔ (∃ k, k ≤ i ∧ P k) ∨ P (i + 1) := by
  constructor
  · rintro ⟨k, hk, hp⟩
    by_cases h : k ≤ i
    · exact Or.inl ⟨k, h, hp⟩
    · have : k = i + 1 := by omega
      subst this; exact Or.inr hp
  · rintro (⟨k, hk, hp⟩ | hp)
    · exact ⟨k, by omega, hp⟩
    · exact ⟨i + 1, le_refl _, hp⟩

theorem forall_le_succ (P : Nat → Prop) (i : Nat) :
    (∀ k, k ≤ i + 1 → P k) ↔ (∀ k, k ≤ i → P k) ∧ P (i + 1) := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega), h _ (le_refl _)⟩
  · rintro ⟨h, hp⟩ k hk
    by_cases h' : k ≤ i
    · exact h k h'
    · have : k = i + 1 := by omega
      subst this; exact hp

theorem toList_getElem_bang {α : Type} [Inhabited α] (s : Array α) (k : Nat) (h : k < s.size) :
    s.toList[k]! = s[k]! := by
  rw [getElem!_pos s.toList k (by simpa using h), getElem!_pos s k h]; simp

theorem forall_mem_toList_iff_idx {α : Type} [Inhabited α] (s : Array α) (P : α → Prop) :
    (∀ x ∈ s.toList, P x) ↔ ∀ k, k < s.size → P s[k]! := by
  rw [forall_mem_iff_idx]
  constructor
  · intro h k hk; have := h k (by simpa using hk); rwa [toList_getElem_bang s k hk] at this
  · intro h k hk; have hk' : k < s.size := by simpa using hk
    rw [toList_getElem_bang s k hk']; exact h k hk'

theorem exists_mem_toList_iff_idx {α : Type} [Inhabited α] (s : Array α) (P : α → Prop) :
    (∃ x ∈ s.toList, P x) ↔ ∃ k, k < s.size ∧ P s[k]! := by
  rw [exists_mem_iff_idx]
  constructor
  · rintro ⟨k, hk, hp⟩; have hk' : k < s.size := by simpa using hk
    exact ⟨k, hk', by rwa [toList_getElem_bang s k hk'] at hp⟩
  · rintro ⟨k, hk, hp⟩; exact ⟨k, by simpa using hk, by rwa [toList_getElem_bang s k hk]⟩

theorem forall_mem_array_iff_idx {α : Type} [Inhabited α] (s : Array α) (P : α → Prop) :
    (∀ x ∈ s, P x) ↔ ∀ k, k < s.size → P s[k]! := by
  have h : (∀ x ∈ s, P x) ↔ ∀ x ∈ s.toList, P x := by simp only [Array.mem_def]
  rw [h]; exact forall_mem_toList_iff_idx s P

theorem exists_mem_array_iff_idx {α : Type} [Inhabited α] (s : Array α) (P : α → Prop) :
    (∃ x ∈ s, P x) ↔ ∃ k, k < s.size ∧ P s[k]! := by
  have h : (∃ x ∈ s, P x) ↔ ∃ x ∈ s.toList, P x := by simp only [Array.mem_def]
  rw [h]; exact exists_mem_toList_iff_idx s P

theorem forall_mem_drop_iff {α : Type} [Inhabited α] (l : List α) (m : Nat) (P : α → Prop) :
    (∀ x ∈ l.drop m, P x) ↔ ∀ k, m ≤ k → k < l.length → P l[k]! := by
  constructor
  · intro h k hmk hk
    have := h (l[k]'hk) (by
      rw [List.mem_iff_getElem]; exact ⟨k - m, by simp; omega, by simp [List.getElem_drop]; congr 1; omega⟩)
    rwa [getElem!_pos l k hk]
  · intro h x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_drop] at hj
    have := h (m + j) (by omega) (by omega)
    rw [getElem!_pos l (m + j) (by omega)] at this
    simpa [List.getElem_drop] using this

theorem exists_mem_drop_iff {α : Type} [Inhabited α] (l : List α) (m : Nat) (P : α → Prop) :
    (∃ x ∈ l.drop m, P x) ↔ ∃ k, m ≤ k ∧ k < l.length ∧ P l[k]! := by
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_drop] at hj
    refine ⟨m + j, by omega, by omega, ?_⟩
    rw [getElem!_pos l (m + j) (by omega)]
    simpa [List.getElem_drop] using hp
  · rintro ⟨k, hmk, hk, hp⟩
    refine ⟨l[k]'hk, ?_, by rwa [getElem!_pos l k hk] at hp⟩
    rw [List.mem_iff_getElem]; exact ⟨k - m, by simp; omega, by simp [List.getElem_drop]; congr 1; omega⟩

theorem forall_mem_take_iff {α : Type} [Inhabited α] (l : List α) (m : Nat) (P : α → Prop) :
    (∀ x ∈ l.take m, P x) ↔ ∀ k, k < m → k < l.length → P l[k]! := by
  constructor
  · intro h k hkm hk
    have := h (l[k]'hk) (by
      rw [List.mem_iff_getElem]; exact ⟨k, by simp; omega, by simp⟩)
    rwa [getElem!_pos l k hk]
  · intro h x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp only [List.length_take] at hj
    have := h j (by omega) (by omega)
    rw [getElem!_pos l j (by omega)] at this
    simpa [List.getElem_take] using this

theorem arr_all_take_iff {α : Type} [Inhabited α] (a : Array α) (n : Nat) (p : α → Bool) :
    (a.take n).all p = true ↔ ∀ k, k < n → k < a.size → p a[k]! = true := by
  have e : (a.take n).toList = a.toList.take n := by simp
  rw [← Array.all_toList, e, List.all_eq_true, forall_mem_take_iff]
  constructor
  · intro h k hk hs; have := h k hk (by simpa using hs); rwa [Refine.toList_getElem_bang a k hs] at this
  · intro h k hk hs; have hs' : k < a.size := by simpa using hs
    rw [Refine.toList_getElem_bang a k hs']; exact h k hk hs'

theorem arr_all_drop_iff {α : Type} [Inhabited α] (a : Array α) (n : Nat) (p : α → Bool) :
    (a.drop n).all p = true ↔ ∀ k, n ≤ k → k < a.size → p a[k]! = true := by
  have e : (a.drop n).toList = a.toList.drop n := by simp
  rw [← Array.all_toList, e, List.all_eq_true, Refine.forall_mem_drop_iff]
  constructor
  · intro h k hk hs; have := h k hk (by simpa using hs); rwa [Refine.toList_getElem_bang a k hs] at this
  · intro h k hk hs; have hs' : k < a.size := by simpa using hs
    rw [Refine.toList_getElem_bang a k hs']; exact h k hk hs'

theorem sorted_arr_le (a : Array Int) (h : List.Pairwise (· ≤ ·) a.toList) :
    ∀ i k, i ≤ k → k < a.size → a[i]! ≤ a[k]! := by
  intro i k hik hk
  rcases Nat.eq_or_lt_of_le hik with rfl | hlt
  · exact le_refl _
  · have := List.pairwise_iff_getElem.mp h i k (by simpa using (by omega : i < a.size)) (by simpa using hk) hlt
    rw [getElem!_pos a i (by omega), getElem!_pos a k hk]
    simpa using this

theorem foldl_max_facts {α : Type} [LinearOrder α] (l : List α) : ∀ (m : α),
    (List.foldl max m l = m ∨ List.foldl max m l ∈ l) ∧ m ≤ List.foldl max m l ∧ ∀ x ∈ l, x ≤ List.foldl max m l := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
    intro m
    obtain ⟨h1, h2, h3⟩ := ih (max m a)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with h | h
      · by_cases hm : m ≤ a
        · right; rw [max_eq_right hm] at h ⊢; rw [h]; simp
        · left
          have hmx : max m a = m := max_eq_left (le_of_lt (not_le.mp hm))
          rw [hmx] at h ⊢; exact h
      · right; exact List.mem_cons_of_mem a h
    · exact le_trans (le_max_left m a) h2
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact le_trans (le_max_right m x) h2
      · exact h3 x hx'

theorem maxlist_nat (L : List Nat) (hne : L ≠ []) :
    L.contains (L.foldl max 0) = true ∧ L.all (fun x => decide (x ≤ L.foldl max 0)) = true := by
  obtain ⟨h1, h2, h3⟩ := foldl_max_facts L 0
  constructor
  · rw [List.contains_iff_mem]
    rcases h1 with h | h
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil L hne
      have hx0 : x = 0 := by have := h3 x hx; omega
      rw [h, ← hx0]; exact hx
    · exact h
  · rw [List.all_eq_true]; intro x hx; simpa using h3 x hx

theorem maxlist_int (L : List Int) (hne : L ≠ []) :
    L.contains (L.foldl max (L.headD 0)) = true ∧ L.all (fun x => decide (x ≤ L.foldl max (L.headD 0))) = true := by
  obtain ⟨h1, h2, h3⟩ := foldl_max_facts L (L.headD 0)
  have hhead : L.headD 0 ∈ L := by
    cases L with
    | nil => exact absurd rfl hne
    | cons a t => simp
  constructor
  · rw [List.contains_iff_mem]
    rcases h1 with h | h
    · rw [h]; exact hhead
    · exact h
  · rw [List.all_eq_true]; intro x hx; simpa using h3 x hx

theorem allsub_nil_mem {α : Type} (xs : List α) : ∀ (acc : List (List α)), [] ∈ acc →
    [] ∈ xs.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) acc := by
  induction xs with
  | nil => intro acc h; simpa using h
  | cons a t ih => intro acc h; exact ih _ (List.mem_append.mpr (Or.inl h))

theorem allsub_nil_mem_arr {α : Type} (xs : Array α) :
    [] ∈ (xs.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]) := by
  rw [← Array.foldl_toList]
  exact allsub_nil_mem xs.toList [[]] (by simp)

theorem allsub_rev_nil_mem {α : Type} (xs : List α) :
    [] ∈ ((xs.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]).map List.reverse) :=
  List.mem_map.mpr ⟨[], allsub_nil_mem xs [[]] (by simp), rfl⟩

theorem longest_facts {α : Type} (L : List (List α)) : ∀ (b : List α),
    (L.foldl (fun best l => if best.length < l.length then l else best) b = b ∨
      L.foldl (fun best l => if best.length < l.length then l else best) b ∈ L) ∧
    b.length ≤ (L.foldl (fun best l => if best.length < l.length then l else best) b).length ∧
    ∀ x ∈ L, x.length ≤ (L.foldl (fun best l => if best.length < l.length then l else best) b).length := by
  induction L with
  | nil => intro b; simp
  | cons a t ih =>
    intro b
    simp only [List.foldl_cons]
    by_cases hlt : b.length < a.length
    · rw [if_pos hlt]
      obtain ⟨h1, h2, h3⟩ := ih a
      refine ⟨?_, by omega, ?_⟩
      · rcases h1 with h | h
        · right; rw [h]; exact List.mem_cons_self
        · right; exact List.mem_cons_of_mem a h
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact h2
        · exact h3 x hx'
    · rw [if_neg hlt]
      obtain ⟨h1, h2, h3⟩ := ih b
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with h | h
        · left; exact h
        · right; exact List.mem_cons_of_mem a h
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · have := h2; omega
        · exact h3 x hx'

theorem longest_spec {α : Type} [BEq α] [LawfulBEq α] (L : List (List α)) (hn : [] ∈ L) :
    L.contains (L.foldl (fun best l => if best.length < l.length then l else best) []) = true ∧
    L.all (fun l => decide (l.length ≤ (L.foldl (fun best l => if best.length < l.length then l else best) []).length)) = true := by
  obtain ⟨h1, h2, h3⟩ := longest_facts L []
  constructor
  · rw [List.contains_iff_mem]
    rcases h1 with h | h
    · rw [h]; exact hn
    · exact h
  · rw [List.all_eq_true]; intro x hx; simpa using h3 x hx

theorem maxlist_int_any (L : List Int) (hne : L ≠ []) :
    L.any (fun s => s == L.foldl max (L.headD 0)) = true ∧ L.all (fun x => decide (x ≤ L.foldl max (L.headD 0))) = true := by
  obtain ⟨h1, h2⟩ := maxlist_int L hne
  refine ⟨?_, h2⟩
  rw [List.contains_iff_mem] at h1
  exact List.any_eq_true.mpr ⟨_, h1, by simp⟩

theorem maxlen_spec {α : Type} (L : List (List α)) (hn : [] ∈ L) :
    L.any (fun a => decide (a.length = (L.map List.length).foldl max 0)) = true ∧
    L.all (fun a => decide (a.length ≤ (L.map List.length).foldl max 0)) = true := by
  have hne : L.map List.length ≠ [] := List.ne_nil_of_mem (a := 0) (List.mem_map.mpr ⟨[], hn, rfl⟩)
  obtain ⟨h1, h2⟩ := maxlist_nat (L.map List.length) hne
  rw [List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨a, ha, hlen⟩ := h1
  constructor
  · exact List.any_eq_true.mpr ⟨a, ha, by simpa using hlen⟩
  · rw [List.all_eq_true]; intro x hx
    have := List.all_eq_true.mp h2 x.length (List.mem_map.mpr ⟨x, hx, rfl⟩)
    simpa using this

theorem filter_pair_le {α : Type} [DecidableEq α] (l : List α) (a b : α) (hab : a ≠ b) :
    (l.filter (fun y => y = a)).length + (l.filter (fun y => y = b)).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hxa : x = a
    · have hxb : ¬ x = b := fun h => hab (hxa.symm.trans h)
      simp [List.filter_cons, hxa, hxb, hab, Ne.symm hab]; omega
    · by_cases hxb : x = b
      · simp [List.filter_cons, hxa, hxb, hab, Ne.symm hab]; omega
      · simp [List.filter_cons, hxa, hxb, hab, Ne.symm hab]; omega

theorem count_pair_le {α : Type} [DecidableEq α] (l : List α) (a b : α) (hab : a ≠ b) :
    l.count a + l.count b ≤ l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hxa : x = a
    · have hxb : ¬ x = b := fun h => hab (hxa.symm.trans h)
      simp [List.count_cons, hxa, hxb, hab, Ne.symm hab]; omega
    · by_cases hxb : x = b
      · simp [List.count_cons, hxa, hxb, hab, Ne.symm hab]; omega
      · simp [List.count_cons, hxa, hxb, hab, Ne.symm hab]; omega

theorem find_some_of_any {α : Type} (l : List α) (p : α → Bool) (h : l.any p = true) :
    ∃ r, l.find? p = some r ∧ r ∈ l ∧ p r = true := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hs : (l.find? p).isSome = true := List.find?_isSome.mpr ⟨x, hx, hp⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨r, hr, List.mem_of_find?_eq_some hr, List.find?_some hr⟩

theorem find_majority {α : Type} [DecidableEq α] [Inhabited α] (xs : List α)
    (h : xs.any (fun x => decide (xs.count x > xs.length / 2)) = true) :
    ∃ r, (xs.find? (fun x => decide (xs.count x > xs.length / 2))).getD default = r ∧ xs.count r > xs.length / 2 ∧
      ∀ x ∈ xs, x ≠ r → xs.count x ≤ xs.length / 2 := by
  obtain ⟨r, hr, hmem, hp⟩ := find_some_of_any xs _ h
  refine ⟨r, by rw [hr]; rfl, of_decide_eq_true hp, ?_⟩
  intro x hx hne
  by_contra hgt
  have h1 := count_pair_le xs x r hne
  have hp' := of_decide_eq_true hp
  omega

theorem ts_inner_step (S : Nat → Nat → Int) (target : Int) (n i j jb : Nat) (ok : Bool)
    (hinv : i + 1 ≤ j ∧ j ≤ n ∧ (ok = true → i < jb ∧ jb < n ∧ S i jb = target ∧ ∀ j', i < j' → j' < jb → S i j' ≠ target) ∧
      (ok = false → ∀ j', i < j' → j' < j → S i j' ≠ target))
    (hg : j < n ∧ ok = false) :
    i + 1 ≤ j + 1 ∧ j + 1 ≤ n ∧
      ((decide (S i j = target) || ok) = true → i < (if S i j = target then j else jb) ∧ (if S i j = target then j else jb) < n ∧
        S i (if S i j = target then j else jb) = target ∧
        ∀ j', i < j' → j' < (if S i j = target then j else jb) → S i j' ≠ target) ∧
      ((decide (S i j = target) || ok) = false → ∀ j', i < j' → j' < j + 1 → S i j' ≠ target) := by
  obtain ⟨hij, hjn, hok1, hok2⟩ := hinv
  obtain ⟨hjlt, hokf⟩ := hg
  subst hokf
  by_cases hs : S i j = target
  · simp only [if_pos hs, decide_eq_true hs, Bool.true_or]
    refine ⟨by omega, by omega, fun _ => ⟨by omega, hjlt, hs, ?_⟩, fun h => by simp at h⟩
    intro j' h1 h2
    exact hok2 rfl j' h1 h2
  · simp only [if_neg hs, decide_eq_false hs, Bool.false_or]
    refine ⟨by omega, by omega, fun hok => by simp at hok, fun _ => ?_⟩
    intro j' h1 h2
    by_cases hje : j' = j
    · subst hje; exact hs
    · exact hok2 rfl j' h1 (by omega)

theorem ts_inner_exit (S : Nat → Nat → Int) (target : Int) (n i j jb : Nat) (ok : Bool)
    (hinv : i + 1 ≤ j ∧ j ≤ n ∧ (ok = true → i < jb ∧ jb < n ∧ S i jb = target ∧ ∀ j', i < j' → j' < jb → S i j' ≠ target) ∧
      (ok = false → ∀ j', i < j' → j' < j → S i j' ≠ target))
    (hn : ¬ (j < n ∧ ok = false)) :
    ((jb, ok).2 = true → i < (jb, ok).1 ∧ (jb, ok).1 < n ∧ S i (jb, ok).1 = target ∧ ∀ j', i < j' → j' < (jb, ok).1 → S i j' ≠ target) ∧
    ((jb, ok).2 = false → ∀ j', i < j' → j' < n → S i j' ≠ target) := by
  obtain ⟨hij, hjn, hok1, hok2⟩ := hinv
  refine ⟨fun h => hok1 h, fun hf => ?_⟩
  have : j = n := by
    by_contra hne
    exact hn ⟨by omega, hf⟩
  subst this
  exact hok2 hf

theorem ts_outer_step (S : Nat → Nat → Int) (target : Int) (n i a b : Nat) (found : Bool) (jr : Nat × Bool)
    (hinv : i ≤ n ∧ (found = true → a < b ∧ b < n ∧ S a b = target ∧
        (∀ i' j', i' < a → i' < j' → j' < n → S i' j' ≠ target) ∧ ∀ j', a < j' → j' < b → S a j' ≠ target) ∧
      (found = false → ∀ i' j', i' < i → i' < j' → j' < n → S i' j' ≠ target))
    (hg : i < n ∧ found = false)
    (hjr : (jr.2 = true → i < jr.1 ∧ jr.1 < n ∧ S i jr.1 = target ∧ ∀ j', i < j' → j' < jr.1 → S i j' ≠ target) ∧
      (jr.2 = false → ∀ j', i < j' → j' < n → S i j' ≠ target)) :
    i + 1 ≤ n ∧ ((jr.2 || found) = true → (if jr.2 = true then i else a) < (if jr.2 = true then jr.1 else b) ∧
        (if jr.2 = true then jr.1 else b) < n ∧
        S (if jr.2 = true then i else a) (if jr.2 = true then jr.1 else b) = target ∧
        (∀ i' j', i' < (if jr.2 = true then i else a) → i' < j' → j' < n → S i' j' ≠ target) ∧
        ∀ j', (if jr.2 = true then i else a) < j' → j' < (if jr.2 = true then jr.1 else b) →
          S (if jr.2 = true then i else a) j' ≠ target) ∧
      ((jr.2 || found) = false → ∀ i' j', i' < i + 1 → i' < j' → j' < n → S i' j' ≠ target) := by
  obtain ⟨hin, hf1, hf2⟩ := hinv
  obtain ⟨hlt, hfound⟩ := hg
  subst hfound
  obtain ⟨hj1, hj2⟩ := hjr
  have hall := hf2 rfl
  cases hb : jr.2 with
  | true =>
    have h := hj1 hb
    simp only [if_true, Bool.true_or]
    refine ⟨by omega, fun _ => ⟨h.1, h.2.1, h.2.2.1, hall, h.2.2.2⟩, fun h' => by simp at h'⟩
  | false =>
    have h := hj2 hb
    simp only [Bool.false_or, Bool.false_eq_true, if_false]
    refine ⟨by omega, fun h' => by simp at h', fun _ => ?_⟩
    intro i' j' hi' hij hjn
    by_cases hie : i' = i
    · subst hie; exact h j' hij hjn
    · exact hall i' j' (by omega) hij hjn
theorem ts_inner_init (S : Nat → Nat → Int) (target : Int) (n i : Nat) (hi : i < n) :
    i + 1 ≤ i + 1 ∧ i + 1 ≤ n ∧ ((false = true) → i < 0 ∧ 0 < n ∧ S i 0 = target ∧ ∀ j', i < j' → j' < 0 → S i j' ≠ target) ∧
      ((false = false) → ∀ j', i < j' → j' < i + 1 → S i j' ≠ target) := by
  refine ⟨le_refl _, by omega, fun h => by simp at h, fun _ j' h1 h2 => by omega⟩

theorem ts_outer_init (S : Nat → Nat → Int) (target : Int) (n : Nat) :
    0 ≤ n ∧ ((false = true) → 0 < 0 ∧ 0 < n ∧ S 0 0 = target ∧
        (∀ i' j', i' < 0 → i' < j' → j' < n → S i' j' ≠ target) ∧ ∀ j', 0 < j' → j' < 0 → S 0 j' ≠ target) ∧
      ((false = false) → ∀ i' j', i' < 0 → i' < j' → j' < n → S i' j' ≠ target) := by
  refine ⟨Nat.zero_le _, fun h => by simp at h, fun _ i' j' h1 _ _ => by omega⟩

theorem ts_lex_all (l : List Int) (target : Int) (a b : Nat) (hb : b < l.length)
    (h1 : ∀ i' j', i' < a → i' < j' → j' < l.length → l[i']! + l[j']! ≠ target)
    (h2 : ∀ j', a < j' → j' < b → l[a]! + l[j']! ≠ target) :
    ((l.take a).zipIdx.all (fun ⟨x, i'⟩ => (l.drop (i' + 1)).all (fun y => x + y ≠ target))) = true ∧
    (((l.drop (a + 1)).take (b - a - 1)).all (fun y => l[a]! + y ≠ target)) = true := by
  constructor
  · rw [List.all_eq_true]
    rintro ⟨x, i'⟩ hx
    have hx' := List.mem_zipIdx_iff_getElem?.mp hx
    simp only at hx'
    obtain ⟨hi'a, hxe⟩ : i' < a ∧ l[i']? = some x := by
      have hlt : i' < (l.take a).length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hx'; simp at hx'
      have hl : (l.take a).length = min a l.length := by simp
      refine ⟨by omega, ?_⟩
      rw [List.getElem?_take_of_lt (by omega)] at hx'
      exact hx'
    simp only [decide_eq_true_eq, List.all_eq_true]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_drop] at hk
    have hxv : x = l[i']! := by
      have : i' < l.length := by omega
      rw [getElem!_pos l i' this]; rw [List.getElem?_eq_getElem this] at hxe; simpa using hxe.symm
    have := h1 i' (i' + 1 + k) hi'a (by omega) (by omega)
    rw [List.getElem_drop]
    rw [getElem!_pos l (i'+1+k) (by omega)] at this
    simpa [hxv] using this
  · rw [List.all_eq_true]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_take, List.length_drop] at hk
    have := h2 (a + 1 + k) (by omega) (by omega)
    rw [getElem!_pos l (a+1+k) (by omega)] at this
    simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
    exact this

theorem ts_pairwise_none (l : List Int) (target : Int)
    (h : ∀ i j, i < j → j < l.length → l[i]! + l[j]! ≠ target) : List.Pairwise (· + · ≠ target) l := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := h i j hij hj
  rw [getElem!_pos l i hi, getElem!_pos l j hj] at this
  exact this

end Refine

@[reducible, simp]
def digits_precond (n : Nat) : Prop :=
  n ≥ 1

@[reducible, simp]
def digits_postcond (n : Nat) (result: Nat) (h_precond : digits_precond (n)) :=
  let ds := (toString n).toList.map (fun c => c.toNat - 48)
  result = (if ds.any (fun d => d % 2 = 1) then (ds.filter (fun d => d % 2 = 1)).prod else 0)



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.string_length_mk, Refine.string_toList_mk, Refine.filter_take_succ_bang, Refine.sorted_filter_range, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))


set_option maxHeartbeats 1000000 in
def digits_derived (n : Nat) (h_precond : digits_precond n) : { ρ : Nat // digits_postcond n ρ h_precond } :=
  ⟨(if ((toString n).toList.map (fun c => c.toNat - 48)).any (fun d => d % 2 = 1) then (((toString n).toList.map (fun c => c.toNat - 48)).filter (fun d => d % 2 = 1)).prod else 0), by refine_auto⟩

def digits (n : Nat) (h_precond : digits_precond n) : Nat := (digits_derived n h_precond).val

theorem digits_spec_satisfied (n : Nat) (h_precond : digits_precond n) :
    digits_postcond n (digits n h_precond) h_precond := (digits_derived n h_precond).property

#print axioms digits_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((digits (5) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (5))
set_option maxHeartbeats 2000000 in
#eval (((digits (54) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (5))
set_option maxHeartbeats 2000000 in
#eval (((digits (120) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (1))
set_option maxHeartbeats 2000000 in
#eval (((digits (5014) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (5))
set_option maxHeartbeats 2000000 in
#eval (((digits (98765) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (315))
set_option maxHeartbeats 2000000 in
#eval (((digits (5576543) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (2625))
set_option maxHeartbeats 2000000 in
#eval (((digits (2468) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (0))
set_option maxHeartbeats 2000000 in
#eval (((digits (951) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (45))
set_option maxHeartbeats 2000000 in
#eval (((digits (247) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (7))
set_option maxHeartbeats 2000000 in
#eval (((digits (182137) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (21))
set_option maxHeartbeats 2000000 in
#eval (((digits (894) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (9))
set_option maxHeartbeats 2000000 in
#eval (((digits (109) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (9))
set_option maxHeartbeats 2000000 in
#eval (((digits (123456789) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (945))
set_option maxHeartbeats 2000000 in
#eval (((digits (13577) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (735))
set_option maxHeartbeats 2000000 in
#eval (((digits (76) (by first | native_decide | trivial | (norm_num [digits_precond]; done) | (simp [digits_precond]; done) | decide | omega))) == (7))
