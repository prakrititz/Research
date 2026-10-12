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

theorem take_succ_bang {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]!] := by
  rw [List.take_succ_eq_append_getElem h, getElem!_pos l i h]

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

end Refine

@[reducible, simp]
def largestSmallestIntegers_precond (lst : List Int) : Prop :=
  True

@[reducible, simp]
def largestSmallestIntegers_postcond (lst : List Int) (result: Option Int × Option Int) (h_precond : largestSmallestIntegers_precond (lst)) :=
  ((result.1 = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ a ∈ lst, result.1 = some a ∧ a < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ a)) ∧
    ((result.2 = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ b ∈ lst, result.2 = some b ∧ 0 < b ∧ ∀ x ∈ lst, 0 < x → b ≤ x))

set_option maxHeartbeats 400000 in
theorem neg_exit : ∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! < 0) → (f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < lst.length → lst[k]! < 0 → lst[k]! ≤ m) → (((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, (if f = true then some m else none) = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y)) := by
  intro lst m f h1 h2
  by_cases hf : f = true
  · right
    obtain ⟨⟨k, hk, hkm⟩, hm, hall⟩ := h2 hf
    refine ⟨m, ?_, by simp [hf], hm, ?_⟩
    · rw [← hkm]; exact Refine.getElem_bang_mem lst k hk
    · intro x hx hx0
      obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx
      exact hall j hj hx0
  · left
    refine ⟨by simp [hf], ?_⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx
    by_contra hneg
    exact hf (h1.mpr ⟨j, hj, by omega⟩)

set_option maxHeartbeats 400000 in
theorem pos_exit : ∀ (lst : List Int) (m : Int) (f : Bool), (f = true ↔ ∃ k, k < lst.length ∧ lst[k]! > 0) → (f = true → (∃ k, k < lst.length ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < lst.length → lst[k]! > 0 → m ≤ lst[k]!) → (((if f = true then some m else none) = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, (if f = true then some m else none) = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x)) := by
  intro lst m f h1 h2
  by_cases hf : f = true
  · right
    obtain ⟨⟨k, hk, hkm⟩, hm, hall⟩ := h2 hf
    refine ⟨m, ?_, by simp [hf], hm, ?_⟩
    · rw [← hkm]; exact Refine.getElem_bang_mem lst k hk
    · intro x hx hx0
      obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx
      exact hall j hj hx0
  · left
    refine ⟨by simp [hf], ?_⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx lst x).mp hx
    by_contra hpos
    exact hf (h1.mpr ⟨j, hj, by omega⟩)


macro "refine_auto" : tactic => `(tactic| (first | (apply neg_exit; all_goals first | done | (simp_all; done) | omega | grind) | (apply pos_exit; all_goals first | done | (simp_all; done) | omega | grind) | ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (apply neg_exit <;> simp_all) | (apply pos_exit <;> simp_all) | (grind [neg_exit, pos_exit]) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, neg_exit, pos_exit] <;> grind [neg_exit, pos_exit]) | nlinarith | (aesop; done)))))

def loop2 (lst : List Int) (h_precond : largestSmallestIntegers_precond lst) (i : Nat) (m : Int) (f : Bool) (h2i : (i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! < 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < i → lst[k]! < 0 → lst[k]! ≤ m))) : { ρ : Option Int // (fun (a : Option Int) => (a = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, a = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y)) ρ } :=
  if h2g : (i < lst.length) then
    match (⟨((i + 1, if lst[i]! < 0 ∧ (f = false ∨ m < lst[i]!) then lst[i]! else m, f || decide (lst[i]! < 0))), by refine_auto⟩ : { ρ : Nat × Int × Bool // (fun (i : Nat) (m : Int) (f : Bool) => i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! < 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ m < 0 ∧ ∀ k, k < i → lst[k]! < 0 → lst[k]! ≤ m)) (ρ).1 (ρ).2.1 (ρ).2.2 ∧ (fun (i : Nat) (m : Int) (f : Bool) => lst.length - i) (ρ).1 (ρ).2.1 (ρ).2.2 < (lst.length - i) }) with
    | ⟨(i', m', f'), h2b⟩ => loop2 lst h_precond i' m' f' h2b.1
  else ⟨(if f = true then some m else none), by first | (have hEq : i = (lst.length) := (by omega); subst hEq; refine_auto) | (refine_auto)⟩
termination_by lst.length - i
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h2b.2 | omega)

def loop5 (lst : List Int) (a : Option Int) (h_precond : largestSmallestIntegers_precond lst) (h1 : ((a = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, a = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y))) (i : Nat) (m : Int) (f : Bool) (h5i : (i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! > 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < i → lst[k]! > 0 → m ≤ lst[k]!))) : { ρ : Option Int // (fun (b : Option Int) => (b = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, b = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x)) ρ } :=
  if h5g : (i < lst.length) then
    match (⟨((i + 1, if lst[i]! > 0 ∧ (f = false ∨ lst[i]! < m) then lst[i]! else m, f || decide (lst[i]! > 0))), by refine_auto⟩ : { ρ : Nat × Int × Bool // (fun (i : Nat) (m : Int) (f : Bool) => i ≤ lst.length ∧ (f = true ↔ ∃ k, k < i ∧ lst[k]! > 0) ∧ (f = true → (∃ k, k < i ∧ lst[k]! = m) ∧ 0 < m ∧ ∀ k, k < i → lst[k]! > 0 → m ≤ lst[k]!)) (ρ).1 (ρ).2.1 (ρ).2.2 ∧ (fun (i : Nat) (m : Int) (f : Bool) => lst.length - i) (ρ).1 (ρ).2.1 (ρ).2.2 < (lst.length - i) }) with
    | ⟨(i', m', f'), h5b⟩ => loop5 lst a h_precond h1 i' m' f' h5b.1
  else ⟨(if f = true then some m else none), by first | (have hEq : i = (lst.length) := (by omega); subst hEq; refine_auto) | (refine_auto)⟩
termination_by lst.length - i
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h5b.2 | omega)


set_option maxHeartbeats 1000000 in
def largestSmallestIntegers_derived (lst : List Int) (h_precond : largestSmallestIntegers_precond lst) : { ρ : Option Int × Option Int // largestSmallestIntegers_postcond lst ρ h_precond } :=
  (match ((loop2 lst h_precond (0) (0) (false) (by refine_auto)) : { a : Option Int // (a = none ∧ ∀ x ∈ lst, x ≥ 0) ∨ (∃ y ∈ lst, a = some y ∧ y < 0 ∧ ∀ x ∈ lst, x < 0 → x ≤ y) }) with | ⟨a, h1⟩ => (match ((loop5 lst a h_precond h1 (0) (0) (false) (by refine_auto)) : { b : Option Int // (b = none ∧ ∀ x ∈ lst, x ≤ 0) ∨ (∃ y ∈ lst, b = some y ∧ 0 < y ∧ ∀ x ∈ lst, 0 < x → y ≤ x) }) with | ⟨b, h3⟩ => ⟨((a, b)), by refine_auto⟩))

def largestSmallestIntegers (lst : List Int) (h_precond : largestSmallestIntegers_precond lst) : Option Int × Option Int := (largestSmallestIntegers_derived lst h_precond).val

theorem largestSmallestIntegers_spec_satisfied (lst : List Int) (h_precond : largestSmallestIntegers_precond lst) :
    largestSmallestIntegers_postcond lst (largestSmallestIntegers lst h_precond) h_precond := (largestSmallestIntegers_derived lst h_precond).property

#print axioms largestSmallestIntegers_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([2, 4, 1, 3, 5, 7]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((none, some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([2, 4, 1, 3, 5, 7, 0]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((none, some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([1, 3, 2, 4, 5, 6, -2]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-2), some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([4, 5, 3, 6, 2, 7, -7]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-7), some (2))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([7, 3, 8, 4, 9, 2, 5, -9]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-9), some (2))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((none, none)))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([0]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((none, none)))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-1, -3, -5, -6]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-1), none)))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-1, -3, -5, -6, 0]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-1), none)))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-6, -4, -4, -3, 1]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-3), some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-6, -4, -4, -3, -100, 1]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-3), some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([9, -4, -6, 5, 0, -2]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-2), some (5))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([0, 0, -1, -3, -7, 2, 4, -7]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-1), some (2))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-7, 1, -5, 0, 0, -3, -16, 2, -9, 0]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-3), some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([-10, -20, -20, 1, 10, 3, 0]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-10), some (1))))
set_option maxHeartbeats 2000000 in
#eval (((largestSmallestIntegers ([5, -11, 1, -17, 10, 5, 0, -20, -17]) (by first | native_decide | trivial | (norm_num [largestSmallestIntegers_precond]; done) | (simp [largestSmallestIntegers_precond]; done) | decide | omega))) == ((some (-11), some (1))))
