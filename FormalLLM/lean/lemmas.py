r"""Lemmas the tactic cascade may use, proved once in Lean (no ``sorry``; ``tests/test_lean_core.py`` checks that).

Each lemma is here because an obligation of a real derivation needed it and the stock cascade did not close the goal
(``benchmarks/datasets/lean_oracle.py`` lists such obligations; ``Reading Material/24`` has the table). They bridge the two ways a
list property is written: by members (``∀ x ∈ l, …``, how people state a specification) and by index (``∀ i, i < l.length →
… l[i]! …``, how an invariant over a counter is stated), and they unfold the prefix ``l.take (i + 1)`` by one element.
"""

LEMMAS = r'''
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


-- general facts added 2026-10-27 from the prover-ceiling scoreboard (indexing a mapped range or an append, sorted
-- and duplicate-free lists): the human helper lemmas of he_009, he_005, he_034 and others are instances of these
theorem getElem_bang_map_range {α : Type} [Inhabited α] (f : Nat → α) (n i : Nat) (h : i < n) :
    ((List.range n).map f)[i]! = f i := by
  have hl : i < ((List.range n).map f).length := by simp; exact h
  rw [getElem!_pos _ i hl]
  simp

theorem getElem_bang_append {α : Type} [Inhabited α] (a b : List α) (j : Nat) :
    (a ++ b)[j]! = if j < a.length then a[j]! else b[j - a.length]! := by
  by_cases h : j < a.length
  · rw [if_pos h, getElem!_pos (a ++ b) j (by simp; omega), getElem!_pos a j h]
    simp [List.getElem_append_left h]
  · rw [if_neg h]
    by_cases h2 : j < (a ++ b).length
    · have h3 : j - a.length < b.length := by simp at h2; omega
      rw [getElem!_pos (a ++ b) j h2, getElem!_pos b (j - a.length) h3]
      simp [List.getElem_append_right (by omega : a.length ≤ j)]
    · have h3 : ¬ (j - a.length < b.length) := by simp at h2; omega
      rw [getElem!_neg (a ++ b) j h2, getElem!_neg b (j - a.length) h3]

theorem pairwise_le_nodup_lt (s : List Int) (hs : s.Pairwise (· ≤ ·)) (hn : s.Nodup) :
    ∀ i, i < s.length - 1 → s[i]! < s[i + 1]! := by
  intro i hi
  have h1 : i < s.length := by omega
  have h2 : i + 1 < s.length := by omega
  rw [getElem!_pos s i h1, getElem!_pos s (i + 1) h2]
  have hle : s[i] ≤ s[i + 1] := List.pairwise_iff_getElem.mp hs i (i + 1) h1 h2 (by omega)
  have hne : s[i] ≠ s[i + 1] := by
    intro heq
    have := (List.Nodup.getElem_inj_iff hn).mp heq
    omega
  omega

theorem dedup_mergeSort_strict (l : List Int) :
    ∀ i, i < (l.dedup.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i]! < (l.dedup.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  apply pairwise_le_nodup_lt
  · have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l.dedup
    simpa using this
  · exact (List.mergeSort_perm l.dedup _).nodup_iff.mpr (List.nodup_dedup l)

theorem mem_dedup_mergeSort (l : List Int) (x : Int) :
    x ∈ l.dedup.mergeSort (fun a b => decide (a ≤ b)) ↔ x ∈ l := by
  rw [(List.mergeSort_perm l.dedup _).mem_iff, List.mem_dedup]


-- the maximum of a list (55 of the 281 human helper lemmas were about `foldl max`), stated so that the automation
-- can use them directly
theorem foldl_max_mem_of_mem {α : Type} [LinearOrder α] (l : List α) (m : α) (h : m ∈ l) : List.foldl max m l ∈ l := by
  rcases (foldl_max_facts l m).1 with h1 | h1
  · rw [h1]; exact h
  · exact h1

theorem le_foldl_max {α : Type} [LinearOrder α] (l : List α) (m x : α) (h : x ∈ l) : x ≤ List.foldl max m l :=
  (foldl_max_facts l m).2.2 x h

theorem start_le_foldl_max {α : Type} [LinearOrder α] (l : List α) (m : α) : m ≤ List.foldl max m l :=
  (foldl_max_facts l m).2.1

theorem getElem_bang_zero_mem_take {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : l ≠ []) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => contradiction
  | cons x xs => simp

theorem getElem_bang_zero_mem_take' {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : 0 < l.length) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

theorem getElem_bang_zero_mem_take_of_lt {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[0]! ∈ l.take (i + 1) := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

-- indexing into a list literal / cons (he_005: `[d, x][2k+1 - len]!`)
theorem getElem_bang_cons {α : Type} [Inhabited α] (x : α) (xs : List α) (j : Nat) :
    (x :: xs)[j]! = if j = 0 then x else xs[j - 1]! := by
  cases j with
  | zero => simp
  | succ n => simp
theorem getElem_bang_nil {α : Type} [Inhabited α] (j : Nat) : ([] : List α)[j]! = default := by simp

-- sorting: mergeSort is a permutation and is ordered (8 open HumanEval tasks reduce to these)
theorem mergeSort_isPerm {α : Type} [BEq α] [LawfulBEq α] (l : List α) (f : α → α → Bool) :
    (l.mergeSort f).isPerm l = true := by
  rw [List.isPerm_iff]
  exact List.mergeSort_perm l f

theorem isPerm_mergeSort {α : Type} [BEq α] [LawfulBEq α] (l : List α) (f : α → α → Bool) :
    l.isPerm (l.mergeSort f) = true := by
  rw [List.isPerm_iff]
  exact (List.mergeSort_perm l f).symm

theorem mergeSort_sorted_by {α : Type} [Inhabited α] (l : List α) (f : α → α → Bool)
    (trans : ∀ a b c, f a b = true → f b c = true → f a c = true) (total : ∀ a b, (f a b || f b a) = true) :
    ∀ i, i < (l.mergeSort f).length - 1 → f (l.mergeSort f)[i]! (l.mergeSort f)[i + 1]! = true := by
  intro i hi
  have hs := List.pairwise_mergeSort trans total l
  have h1 : i < (l.mergeSort f).length := by omega
  have h2 : i + 1 < (l.mergeSort f).length := by omega
  rw [getElem!_pos _ i h1, getElem!_pos _ (i + 1) h2]
  exact List.pairwise_iff_getElem.mp hs i (i + 1) h1 h2 (by omega)

theorem mergeSort_le_int (l : List Int) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_ge_int (l : List Int) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≥ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (l.mergeSort (fun a b => decide (a ≥ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_le_nat (l : List Nat) :
    ∀ i, i < (l.mergeSort (fun a b => decide (a ≤ b))).length - 1 →
      (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_key_le {α : Type} [Inhabited α] (key : α → Int) (l : List α) :
    ∀ i, i < (l.mergeSort (fun a b => decide (key a ≤ key b))).length - 1 →
      key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i]! ≤ key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_key_le_nat {α : Type} [Inhabited α] (key : α → Nat) (l : List α) :
    ∀ i, i < (l.mergeSort (fun a b => decide (key a ≤ key b))).length - 1 →
      key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i]! ≤ key (l.mergeSort (fun a b => decide (key a ≤ key b)))[i + 1]! := by
  intro i hi
  have := mergeSort_sorted_by l (fun a b => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega)
    (fun a b => by simp; omega) i hi
  simpa using this

theorem mergeSort_length' {α : Type} (l : List α) (f : α → α → Bool) : (l.mergeSort f).length = l.length :=
  List.length_mergeSort l

theorem mem_mergeSort' {α : Type} (l : List α) (f : α → α → Bool) (x : α) : x ∈ l.mergeSort f ↔ x ∈ l :=
  (List.mergeSort_perm l f).mem_iff

-- divisibility (gcd and friends) and the descending sort on Nat
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

-- the minimum of a list (mirror of the foldl max family)
theorem foldl_min_facts {α : Type} [LinearOrder α] (l : List α) : ∀ (m : α),
    (List.foldl min m l = m ∨ List.foldl min m l ∈ l) ∧ List.foldl min m l ≤ m ∧ ∀ x ∈ l, List.foldl min m l ≤ x := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
    intro m
    simp only [List.foldl_cons, List.mem_cons]
    obtain ⟨h1, h2, h3⟩ := ih (min m a)
    refine ⟨?_, le_trans h2 (min_le_left _ _), ?_⟩
    · rcases h1 with h | h
      · rcases min_choice m a with hm | hm
        · left; rw [h, hm]
        · right; left; rw [h, hm]
      · right; right; exact h
    · rintro x (rfl | hx)
      · exact le_trans h2 (min_le_right _ _)
      · exact h3 x hx
theorem foldl_min_mem_of_mem {α : Type} [LinearOrder α] (l : List α) (m : α) (h : m ∈ l) : List.foldl min m l ∈ l := by
  rcases (foldl_min_facts l m).1 with h1 | h1
  · rw [h1]; exact h
  · exact h1
theorem foldl_min_le {α : Type} [LinearOrder α] (l : List α) (m x : α) (h : x ∈ l) : List.foldl min m l ≤ x :=
  (foldl_min_facts l m).2.2 x h
theorem foldl_min_le_start {α : Type} [LinearOrder α] (l : List α) (m : α) : List.foldl min m l ≤ m :=
  (foldl_min_facts l m).2.1

-- every common divisor is at most the gcd
theorem le_gcd_of_mod_left (a b d : Nat) (ha : 0 < a) (hda : a % d = 0) (hdb : b % d = 0) : d ≤ Nat.gcd a b :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left b ha) (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hda) (Nat.dvd_of_mod_eq_zero hdb))
theorem le_gcd_of_mod_right (a b d : Nat) (hb : 0 < b) (hda : a % d = 0) (hdb : b % d = 0) : d ≤ Nat.gcd a b :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_right a hb) (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hda) (Nat.dvd_of_mod_eq_zero hdb))

-- sorting as a permutation, in the Prop form (List.Perm)
theorem mergeSort_perm' {α : Type} (l : List α) (f : α → α → Bool) : (l.mergeSort f).Perm l := List.mergeSort_perm l f
theorem perm_mergeSort' {α : Type} (l : List α) (f : α → α → Bool) : l.Perm (l.mergeSort f) := (List.mergeSort_perm l f).symm
theorem filter_mergeSort_perm {α : Type} (l : List α) (f : α → α → Bool) (p : α → Bool) :
    ((l.filter p).mergeSort f).Perm (l.filter p) := List.mergeSort_perm _ f

-- counting loops: one more element of the range / prefix
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

-- one more element of a prefix, for any list (no bound needed): builder loops over `take i`
theorem take_succ_getElem? {α : Type} (l : List α) (i : Nat) : l.take (i + 1) = l.take i ++ l[i]?.toList := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih => cases i with
    | zero => simp
    | succ n => simp [List.take_succ_cons, ih]

-- sortedness in the List.Pairwise form (14 open Verina tasks state it this way)
theorem pairwise_mergeSort_le_int (l : List Int) : List.Pairwise (fun a b => a ≤ b) (l.mergeSort (fun a b => decide (a ≤ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_le_nat (l : List Nat) : List.Pairwise (fun a b => a ≤ b) (l.mergeSort (fun a b => decide (a ≤ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_ge_int (l : List Int) : List.Pairwise (fun a b => a ≥ b) (l.mergeSort (fun a b => decide (a ≥ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_ge_nat (l : List Nat) : List.Pairwise (fun a b => a ≥ b) (l.mergeSort (fun a b => decide (a ≥ b))) := by
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≥ b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
theorem pairwise_mergeSort_key_le {α : Type} (key : α → Int) (l : List α) :
    List.Pairwise (fun a b => key a ≤ key b) (l.mergeSort (fun a b => decide (key a ≤ key b))) := by
  have := List.pairwise_mergeSort (le := fun a b : α => decide (key a ≤ key b)) (fun a b c h1 h2 => by simp at *; omega) (fun a b => by simp; omega) l
  simpa using this
-- stability: sorting by a key keeps the order of the elements with equal keys (he_145's "ties keep their original order")
theorem filter_mergeSort_key {α β : Type} [LinearOrder β] (key : α → β) (l : List α) (x : α) :
    List.filter (fun y => key y == key x) (l.mergeSort fun a b => decide (key a ≤ key b)) =
      List.filter (fun y => key y == key x) l := by
  have trans : ∀ a b c : α, decide (key a ≤ key b) = true → decide (key b ≤ key c) = true →
      decide (key a ≤ key c) = true := by
    intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact le_trans h1 h2
  have total : ∀ a b : α, (decide (key a ≤ key b) || decide (key b ≤ key a)) = true := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _
  have hc : (l.filter fun y => key y == key x).Pairwise (fun a b => decide (key a ≤ key b) = true) := by
    apply List.Pairwise.imp_of_mem (R := fun _ _ => True) _ (List.pairwise_of_forall (by simp))
    intro a b ha hb _
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    simp [ha.2, hb.2]
  have sub := List.sublist_mergeSort trans total hc (List.filter_sublist (l := l))
  have sub' := sub.filter (fun y => key y == key x)
  rw [List.filter_filter] at sub'
  simp only [Bool.and_self] at sub'
  symm
  apply sub'.eq_of_length
  exact ((List.mergeSort_perm l _).filter _).length_eq.symm
-- the same for keys in `Int` / `Nat`: a goal's `decide (key a ≤ key b)` uses the type's own `Decidable` instance, which the
-- general statement (over `LinearOrder`) does not match syntactically (he_145)
theorem filter_mergeSort_key_int {α : Type} (key : α → Int) (l : List α) (x : α) :
    List.filter (fun y => key y == key x) (l.mergeSort fun a b => decide (key a ≤ key b)) =
      List.filter (fun y => key y == key x) l := by
  have := filter_mergeSort_key key l x
  convert this using 3 <;> rw [Bool.eq_iff_iff] <;> simp
theorem filter_mergeSort_key_nat {α : Type} (key : α → Nat) (l : List α) (x : α) :
    List.filter (fun y => key y == key x) (l.mergeSort fun a b => decide (key a ≤ key b)) =
      List.filter (fun y => key y == key x) l := by
  have := filter_mergeSort_key key l x
  convert this using 3 <;> rw [Bool.eq_iff_iff] <;> simp
-- the digits `Nat.toDigits b n` writes (2 ≤ b ≤ 10) are decimal digit characters below `b` (he_044)
theorem digitChar_toNat (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  interval_cases d <;> rfl
theorem mem_toDigits_lt (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) (c : Char) (hc : c ∈ Nat.toDigits b n) :
    c.toNat - 48 < b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if hb] at hc
    split at hc
    · simp at hc; subst hc; rw [digitChar_toNat n (by omega)]; omega
    · simp at hc
      rcases hc with hc | hc
      · exact ih (n / b) (Nat.div_lt_self (by omega) hb) hc
      · subst hc
        rw [digitChar_toNat _ (by have := Nat.mod_lt n (by omega : b > 0); omega)]
        have := Nat.mod_lt n (by omega : b > 0); omega
theorem toDigits_all_digit (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) :
    ((Nat.toDigits b n).all fun c => c.isDigit && decide (c.toNat - '0'.toNat < b)) = true := by
  rw [List.all_eq_true]; intro c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.isDigit_of_mem_toDigits (by omega) hb10 hc, mem_toDigits_lt b n hb hb10 c hc⟩
-- the same by index: the form the simp set turns `List.all` into
theorem toDigits_idx_digit (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) : ∀ (k : Nat) (h : k < (Nat.toDigits b n).length),
    (Nat.toDigits b n)[k].isDigit = true ∧ (Nat.toDigits b n)[k].toNat - 48 < b := fun _ h =>
  ⟨Nat.isDigit_of_mem_toDigits (by omega) hb10 (List.getElem_mem h), mem_toDigits_lt b n hb hb10 _ (List.getElem_mem h)⟩
-- reading the digits back (most significant first) gives the number; for `n > 0` the first digit is not `'0'` (he_044)
theorem foldl_toDigits (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) :
    (Nat.toDigits b n).foldl (fun acc c => acc * b + (c.toNat - '0'.toNat)) 0 = n := by
  have h := Nat.ofDigitChars_toDigits (n := n) hb hb10
  rw [Nat.ofDigitChars_eq_foldl] at h
  have e : (fun acc c => acc * b + (c.toNat - '0'.toNat)) = (fun sofar (c : Char) => b * sofar + (c.toNat - '0'.toNat)) := by
    funext a c; rw [Nat.mul_comm]
  rw [e]; exact h
theorem foldl_toDigits' (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) :
    (Nat.toDigits b n).foldl (fun acc c => acc * b + (c.toNat - 48)) 0 = n :=
  foldl_toDigits b n hb hb10
theorem toDigits_head_ne_zero (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) (hn : 0 < n) : (Nat.toDigits b n).head! ≠ '0' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [Nat.toDigits_eq_if hb]
    split
    · have : n < 10 := by omega
      simp only [List.head!_cons]
      interval_cases n <;> decide
    · have hq : 0 < n / b := Nat.div_pos (by omega) (by omega)
      obtain ⟨c, cs, h⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := n / b) (b := b))
      have ih' := ih (n / b) (Nat.div_lt_self (by omega) hb) hq
      rw [h] at ih' ⊢
      simpa using ih'
-- the same by index (the simp set writes `l.head!` as `l[0]!`)
theorem toDigits_getElem_zero_ne_zero (b n : Nat) (hb : 1 < b) (hb10 : b ≤ 10) (hn : 0 < n) :
    ¬ (Nat.toDigits b n)[0]! = '0' := by
  have := toDigits_head_ne_zero b n hb hb10 hn
  rwa [head_bang_eq _ Nat.toDigits_ne_nil] at this
-- trial division: the least divisor `d ≥ 2` of `n` is prime; what is left, `n / d`, has no smaller divisor either, and is 1
-- or at least `d` (he_025; he_059)
theorem prime_of_min_divisor (d n : Nat) (hd : 2 ≤ d) (hdvd : n % d = 0) (hmin : ∀ k, 2 ≤ k → k < d → ¬ k ∣ n) :
    Nat.Prime d := by
  refine Nat.prime_def.mpr ⟨hd, fun m hm => ?_⟩
  by_contra h
  push_neg at h
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm (by omega)
  have hle : m ≤ d := Nat.le_of_dvd (by omega) hm
  exact hmin m (by omega) (by omega) (Nat.dvd_trans hm (Nat.dvd_of_mod_eq_zero hdvd))
theorem not_dvd_div_of_not_dvd (k d n : Nat) (hdvd : n % d = 0) (h : ¬ k ∣ n) : ¬ k ∣ n / d :=
  fun hk => h (Nat.dvd_trans hk (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hdvd)))
theorem div_one_or_ge_of_min_divisor (d n : Nat) (hd : 2 ≤ d) (hn : 0 < n) (hdvd : n % d = 0)
    (hmin : ∀ k, 2 ≤ k → k < d → ¬ k ∣ n) : n / d = 1 ∨ d ≤ n / d := by
  have hq : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mod_eq_zero hdvd)) (by omega)
  by_cases h1 : n / d = 1
  · exact Or.inl h1
  · right
    by_contra hlt
    exact hmin (n / d) (by omega) (by omega) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hdvd))
-- a list sorted by index stays sorted after appending an element at least as large as every member
theorem sorted_append_ge {α : Type} [LinearOrder α] [Inhabited α] (l : List α) (d : α)
    (hs : ∀ i, i < l.length - 1 → l[i]! ≤ l[i + 1]!) (hd : ∀ p ∈ l, p ≤ d) :
    ∀ i, i < (l ++ [d]).length - 1 → (l ++ [d])[i]! ≤ (l ++ [d])[i + 1]! := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  have hi1 : i < l.length := by omega
  rw [getElem!_pos (l ++ [d]) i (by simp; omega), getElem!_pos (l ++ [d]) (i + 1) (by simp; omega),
    List.getElem_append_left hi1]
  by_cases h : i + 1 < l.length
  · rw [List.getElem_append_left h]
    have := hs i (by omega)
    rwa [getElem!_pos l i hi1, getElem!_pos l (i + 1) h] at this
  · have e : i + 1 = l.length := by omega
    simp only [e, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact hd _ (List.getElem_mem hi1)
-- lists of characters turned into strings and back (`String.mk` is deprecated, and the simp set has no rule for the round
-- trip under `map`: he_001)
theorem map_toList_mk (l : List (List Char)) : (l.map String.mk).map String.toList = l := by
  induction l <;> simp_all [string_toList_mk]
theorem map_comp_toList_mk (l : List (List Char)) : l.map (String.toList ∘ String.mk) = l := by
  induction l <;> simp_all [string_toList_mk]
-- counting two symbols: equal counts in every part give equal counts in the whole; a list whose every non-empty prefix
-- has more `a`s than `b`s but equal totals is empty; so splitting a balanced list into balanced groups leaves no rest
-- (he_001: bracket groups)
theorem count_flatten_eq {α : Type} [BEq α] (a b : α) (G : List (List α)) (h : ∀ g ∈ G, g.count a = g.count b) :
    G.flatten.count a = G.flatten.count b := by
  induction G with
  | nil => simp
  | cons g G ih =>
    simp only [List.flatten_cons, List.count_append]
    rw [h g List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem g hx))]
theorem rest_nil_of_counts {α : Type} [BEq α] (a b : α) (c : List α) (heq : c.count a = c.count b)
    (hlt : ∀ k, 0 < k → k ≤ c.length → (c.take k).count b < (c.take k).count a) : c = [] := by
  by_contra h
  have := hlt c.length (List.length_pos_iff.mpr h) (Nat.le_refl _)
  rw [List.take_length] at this
  omega
-- (the prefix condition first: matched against a hypothesis by `apply`, it fixes `a`, `b` and `c` for the others)
theorem flatten_eq_of_balanced {α : Type} [BEq α] (a b : α) (G : List (List α)) (c L : List α)
    (hc : ∀ k, 0 < k → k ≤ c.length → (c.take k).count b < (c.take k).count a)
    (h : G.flatten ++ c = L) (hL : L.count a = L.count b) (hG : ∀ g ∈ G, g.count a = g.count b) : G.flatten = L := by
  have hf := count_flatten_eq a b G hG
  have hca : c.count a = c.count b := by
    rw [← h, List.count_append, List.count_append] at hL
    omega
  rw [rest_nil_of_counts a b c hca hc, List.append_nil] at h
  exact h
-- closing a group: if every non-empty prefix of `cur` has more `a`s than `b`s and `cur ++ [x]` has equal counts, then
-- `cur ++ [x]` is balanced (no prefix has more `b`s; equal counts) and no proper non-empty prefix of it is (he_001)
theorem closed_group_balanced {α : Type} [BEq α] (a b x : α) (cur : List α)
    (hc : ∀ k, 0 < k → k ≤ cur.length → (cur.take k).count b < (cur.take k).count a)
    (heq : (cur ++ [x]).count a = (cur ++ [x]).count b) :
    (∀ k, k ≤ (cur ++ [x]).length → ((cur ++ [x]).take k).count b ≤ ((cur ++ [x]).take k).count a) ∧
      (cur ++ [x]).count a = (cur ++ [x]).count b := by
  refine ⟨fun k hk => ?_, heq⟩
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k ≤ cur.length
  · rw [List.take_append_of_le_length hk']
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · exact Nat.le_of_lt (hc k hpos hk')
  · have e : k = cur.length + 1 := by omega
    subst e
    rw [List.take_of_length_le (by simp)]
    omega
-- its first half alone (a goal split at `∧` asks for the halves separately)
theorem closed_group_prefix {α : Type} [BEq α] (a b x : α) (cur : List α)
    (hc : ∀ k, 0 < k → k ≤ cur.length → (cur.take k).count b < (cur.take k).count a)
    (heq : (cur ++ [x]).count a = (cur ++ [x]).count b) :
    ∀ k, k ≤ (cur ++ [x]).length → ((cur ++ [x]).take k).count b ≤ ((cur ++ [x]).take k).count a :=
  (closed_group_balanced a b x cur hc heq).1
theorem closed_group_minimal {α : Type} [BEq α] (a b x : α) (cur : List α)
    (hc : ∀ k, 0 < k → k ≤ cur.length → (cur.take k).count b < (cur.take k).count a) :
    ∀ k < (cur ++ [x]).length, 0 < k →
      ¬((∀ j, j ≤ ((cur ++ [x]).take k).length →
          (((cur ++ [x]).take k).take j).count b ≤ (((cur ++ [x]).take k).take j).count a) ∧
        ((cur ++ [x]).take k).count a = ((cur ++ [x]).take k).count b) := by
  intro k hk hpos ⟨_, h⟩
  simp only [List.length_append, List.length_singleton] at hk
  rw [List.take_append_of_le_length (by omega)] at h
  have := hc k hpos (by omega)
  omega
-- extending an open group: the next symbol `L[i]` keeps every non-empty prefix of `cur ++ [L[i]]` strictly open when the
-- whole of `cur ++ [L[i]]` is not balanced (the prefix `L.take (i + 1)` = closed groups ++ `cur ++ [L[i]]` has no more
-- `b`s than `a`s, and the closed groups have equal counts) (he_001)
theorem open_group_extend {α : Type} [BEq α] [Inhabited α] (a b : α) (G : List (List α)) (cur L : List α) (i : Nat)
    (hc : ∀ k, 0 < k → k ≤ cur.length → (cur.take k).count b < (cur.take k).count a)
    (hflat : G.flatten ++ cur = L.take i) (hi : i < L.length)
    (hne : ¬ (cur ++ [L[i]!]).count a = (cur ++ [L[i]!]).count b)
    (hpre : ∀ k, k ≤ L.length → (L.take k).count b ≤ (L.take k).count a)
    (hG : ∀ g ∈ G, g.count a = g.count b) :
    ∀ k, 0 < k → k ≤ (cur ++ [L[i]!]).length → ((cur ++ [L[i]!]).take k).count b < ((cur ++ [L[i]!]).take k).count a := by
  intro k hk0 hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k ≤ cur.length
  · rw [List.take_append_of_le_length hk']
    exact hc k hk0 hk'
  · have e : k = cur.length + 1 := by omega
    subst e
    rw [List.take_of_length_le (by simp)]
    have hp := hpre (i + 1) (by omega)
    rw [take_succ_bang L i hi, ← hflat, List.append_assoc] at hp
    simp only [List.count_append] at hp hne ⊢
    have hf := count_flatten_eq a b G hG
    omega
-- the same for one prefix length `k` (a goal whose `∀ k` is already introduced)
theorem open_group_extend_at {α : Type} [BEq α] [Inhabited α] (a b : α) (G : List (List α)) (cur L : List α) (i k : Nat)
    (hc : ∀ k, 0 < k → k ≤ cur.length → (cur.take k).count b < (cur.take k).count a)
    (hflat : G.flatten ++ cur = L.take i) (hi : i < L.length)
    (hne : ¬ (cur ++ [L[i]!]).count a = (cur ++ [L[i]!]).count b)
    (hpre : ∀ k, k ≤ L.length → (L.take k).count b ≤ (L.take k).count a)
    (hG : ∀ g ∈ G, g.count a = g.count b) (hk0 : 0 < k) (hk : k ≤ (cur ++ [L[i]!]).length) :
    ((cur ++ [L[i]!]).take k).count b < ((cur ++ [L[i]!]).take k).count a :=
  open_group_extend a b G cur L i hc hflat hi hne hpre hG k hk0 hk
-- the positions `i % m = 0` below `n` (m = 2, 3) are `m * k` for `k < (n + m - 1) / m`
theorem filter_range_mod2 (n : Nat) :
    (List.range n).filter (fun i => decide (i % 2 = 0)) = (List.range ((n + 1) / 2)).map (fun k => 2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : n % 2 = 0
    · have e : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      rw [e, List.range_succ, List.map_append]
      simp [h]; omega
    · have e : (n + 1 + 1) / 2 = (n + 1) / 2 := by omega
      rw [e]; simp [h]
theorem filter_range_mod3 (n : Nat) :
    (List.range n).filter (fun i => decide (i % 3 = 0)) = (List.range ((n + 2) / 3)).map (fun k => 3 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : n % 3 = 0
    · have e : (n + 1 + 2) / 3 = (n + 2) / 3 + 1 := by omega
      rw [e, List.range_succ, List.map_append]
      simp [h]; omega
    · have e : (n + 1 + 2) / 3 = (n + 2) / 3 := by omega
      rw [e]; simp [h]
-- writing `s` into the positions `i % m = 0` and reading those positions back gives `s` (he_033, he_037: sort every
-- third / every second element in place)
theorem gather_scatter2 (l s : List Int)
    (hs : s.length = ((List.range l.length).filter (fun i => decide (i % 2 = 0))).length) :
    ((List.range l.length).filter (fun i => decide (i % 2 = 0))).map
      (fun i => ((List.range l.length).map (fun i => if i % 2 = 0 then s[i / 2]! else l[i]!))[i]!) = s := by
  rw [filter_range_mod2] at hs ⊢
  simp only [List.length_map, List.length_range] at hs
  apply List.ext_getElem (by simp [hs])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hk : 2 * k < l.length := by simp at h1; omega
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp [Nat.mul_mod_right, List.getElem?_eq_getElem h2]
theorem gather_scatter3 (l s : List Int)
    (hs : s.length = ((List.range l.length).filter (fun i => decide (i % 3 = 0))).length) :
    ((List.range l.length).filter (fun i => decide (i % 3 = 0))).map
      (fun i => ((List.range l.length).map (fun i => if i % 3 = 0 then s[i / 3]! else l[i]!))[i]!) = s := by
  rw [filter_range_mod3] at hs ⊢
  simp only [List.length_map, List.length_range] at hs
  apply List.ext_getElem (by simp [hs])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hk : 3 * k < l.length := by simp at h1; omega
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp [Nat.mul_mod_right, List.getElem?_eq_getElem h2]
-- sortedness by index with the bound as a hypothesis (`apply` leaves `i < l.length - 1`, which `simp_all` then sees in
-- whatever form the simplifier gave the length)
theorem mergeSort_le_int' (l : List Int) (i : Nat) (hi : i < l.length - 1) :
    (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! :=
  mergeSort_le_int l i (by simpa using hi)
theorem mergeSort_le_nat' (l : List Nat) (i : Nat) (hi : i < l.length - 1) :
    (l.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (l.mergeSort (fun a b => decide (a ≤ b)))[i + 1]! :=
  mergeSort_le_nat l i (by simpa using hi)

end Refine
'''

#: The lemmas that the cascade passes to ``simp_all``. ``mem_iff_idx`` is left out: it would rewrite every membership,
#: including those a specification states on purpose. ``-List.take_append_getElem`` removes a core simp lemma that folds
#: ``l.take i ++ [l[i]]`` back into ``l.take (i + 1)``: with ``take_succ_bang`` unfolding it, ``simp`` loops (found with
#: ``set_option trace.Meta.Tactic.simp.rewrite true``).
SIMP_SET = ", ".join([f"Refine.{name}" for name in (
    "forall_mem_iff_idx", "exists_mem_iff_idx", "getElem_bang_mem", "getElem_bang_mem_take", "head_mem_take_one", "string_length_mk", "string_toList_mk", "filter_take_succ_bang", "sorted_filter_range", "take_succ_bang", "sum_take_succ_bang", "head_bang_eq",
    "getElem_bang_append_lt", "getElem_bang_append_length", "exists_le_succ", "forall_le_succ",
    "take_string_length", "forall_mem_toList_iff_idx", "exists_mem_toList_iff_idx", "forall_mem_array_iff_idx",
    "exists_mem_array_iff_idx", "getElem_bang_map_range", "mem_dedup_mergeSort", "mergeSort_isPerm", "isPerm_mergeSort", "mem_mergeSort'", "length_filter_range_succ", "filter_mergeSort_key_int", "filter_mergeSort_key_nat", "gather_scatter2", "gather_scatter3", "map_toList_mk", "map_comp_toList_mk")] + ["String.length_toList", "List.range_succ", "-List.take_append_getElem", "-List.getElem!_eq_getElem?_getD"])

NAMES = ("forall_mem_iff_idx", "exists_mem_iff_idx", "getElem_bang_mem", "getElem_bang_mem_take", "head_mem_take_one", "string_length_mk", "string_toList_mk", "filter_take_succ_bang", "sorted_filter_range", "mem_iff_idx", "take_succ_bang", "sum_take_succ_bang", "head_bang_eq",
         "getElem_bang_append_lt", "getElem_bang_append_length", "exists_le_succ", "forall_le_succ", "take_string_length",
         "toList_getElem_bang", "forall_mem_toList_iff_idx", "exists_mem_toList_iff_idx", "forall_mem_array_iff_idx",
         "exists_mem_array_iff_idx", "forall_mem_drop_iff", "exists_mem_drop_iff", "forall_mem_take_iff", "arr_all_take_iff", "arr_all_drop_iff", "sorted_arr_le", "foldl_max_facts", "maxlist_nat", "maxlist_int", "allsub_nil_mem", "allsub_nil_mem_arr", "allsub_rev_nil_mem", "longest_facts", "longest_spec", "maxlist_int_any", "maxlen_spec", "filter_pair_le", "count_pair_le", "find_some_of_any", "find_majority", "ts_inner_init", "ts_outer_init", "ts_inner_step", "ts_inner_exit", "ts_outer_step", "ts_lex_all", "ts_pairwise_none", "getElem_bang_map_range", "getElem_bang_append", "pairwise_le_nodup_lt", "dedup_mergeSort_strict", "mem_dedup_mergeSort", "foldl_max_mem_of_mem", "le_foldl_max", "start_le_foldl_max", "getElem_bang_zero_mem_take", "getElem_bang_zero_mem_take'", "getElem_bang_zero_mem_take_of_lt", "getElem_bang_cons", "getElem_bang_nil", "mergeSort_isPerm", "isPerm_mergeSort", "mergeSort_le_int", "mergeSort_ge_int", "mergeSort_le_nat", "mergeSort_key_le", "mergeSort_key_le_nat", "mergeSort_length'", "mem_mergeSort'", "mod_gcd_left", "mod_gcd_right", "mod_eq_zero_of_dvd'", "dvd_of_mod_eq_zero'", "le_of_dvd_pos", "mergeSort_ge_nat", "foldl_min_facts", "foldl_min_mem_of_mem", "foldl_min_le", "foldl_min_le_start", "le_gcd_of_mod_left", "le_gcd_of_mod_right", "mergeSort_perm'", "perm_mergeSort'", "filter_mergeSort_perm", "length_filter_range_succ", "count_take_succ", "countP_take_succ", "take_succ_getElem?", "pairwise_mergeSort_le_int", "pairwise_mergeSort_le_nat", "pairwise_mergeSort_ge_int", "pairwise_mergeSort_ge_nat", "pairwise_mergeSort_key_le", "filter_mergeSort_key", "filter_mergeSort_key_int", "filter_mergeSort_key_nat", "digitChar_toNat", "mem_toDigits_lt", "toDigits_all_digit", "toDigits_idx_digit", "foldl_toDigits", "foldl_toDigits'", "toDigits_head_ne_zero", "toDigits_getElem_zero_ne_zero", "prime_of_min_divisor", "not_dvd_div_of_not_dvd", "div_one_or_ge_of_min_divisor", "sorted_append_ge", "map_toList_mk", "map_comp_toList_mk", "count_flatten_eq", "rest_nil_of_counts", "flatten_eq_of_balanced", "closed_group_balanced", "closed_group_prefix", "closed_group_minimal", "open_group_extend", "open_group_extend_at", "filter_range_mod2", "filter_range_mod3", "gather_scatter2", "gather_scatter3", "mergeSort_le_int'", "mergeSort_le_nat'")

#: "Evaluation" rewrites only: an index into a construction becomes its value (``((range n).map f)[i]! = f i``). Unlike
#: ``SIMP_SET`` they do not unfold ``take (i + 1)`` or turn ``∀ x ∈ l`` into the index form (right for loop steps, wrong for a
#: closed-form value, where the library lemmas are stated over ``take (i + 1)`` and members): found on he_009, 2026-10-27.
EVAL_SET = ", ".join(["Refine.getElem_bang_map_range", "Refine.getElem_bang_append", "Refine.getElem_bang_cons", "Refine.getElem_bang_nil", "Refine.mergeSort_isPerm", "Refine.isPerm_mergeSort", "Refine.mem_mergeSort'", "Refine.mergeSort_length'", "Refine.mem_dedup_mergeSort", "Refine.toList_getElem_bang",
                      "Refine.string_toList_mk", "Refine.string_length_mk", "List.length_map", "List.length_range"])
