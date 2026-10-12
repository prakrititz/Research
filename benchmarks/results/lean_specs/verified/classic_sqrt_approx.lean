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
def sqrtApprox_precond (N : ℚ) (e : ℚ) : Prop :=
  N ≥ 0 ∧ e > 0

@[reducible, simp]
def sqrtApprox_postcond (N : ℚ) (e : ℚ) (result: ℚ) (h_precond : sqrtApprox_precond (N) (e)) :=
  result ≥ 0 ∧ result * result ≤ N ∧ N < (result + e) * (result + e)

set_option maxHeartbeats 400000 in
theorem floor_bound : ∀ (N e : ℚ) (k : ℕ), 0 ≤ N → 0 < e → ((k + 1 : ℚ) * e) * ((k + 1 : ℚ) * e) ≤ N → ⌊(N + 1) / e⌋₊ + 1 - (k + 1) < ⌊(N + 1) / e⌋₊ + 1 - k := by
  intro N e k hN he h
  have h1 : ((k + 1 : ℚ) * e) ≤ N + 1 := by
    by_cases hle : ((k + 1 : ℚ) * e) ≤ 1
    · linarith
    · push_neg at hle; nlinarith
  have h2 : ((k + 1 : ℕ) : ℚ) ≤ (N + 1) / e := by
    rw [le_div_iff₀ he]; push_cast; exact h1
  have h3 : k + 1 ≤ ⌊(N + 1) / e⌋₊ := Nat.le_floor h2
  omega


macro "refine_auto" : tactic => `(tactic| (first | (apply floor_bound; all_goals first | done | (simp_all; done) | omega | grind) | ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (apply floor_bound <;> simp_all) | (grind [floor_bound]) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, floor_bound] <;> grind [floor_bound]) | nlinarith | (aesop; done)))))

def loop1 (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond N e) (k : Nat) (h1i : (((k : ℚ) * e) * ((k : ℚ) * e) ≤ N)) : { ρ : ℚ // sqrtApprox_postcond N e ρ h_precond } :=
  if h1g : ((((k : ℚ) + 1) * e) * (((k : ℚ) + 1) * e) ≤ N) then
    match (⟨(k + 1), by refine_auto⟩ : { ρ : Nat // (fun (k : Nat) => ((k : ℚ) * e) * ((k : ℚ) * e) ≤ N) (ρ) ∧ (fun (k : Nat) => ⌊(N + 1) / e⌋₊ + 1 - k) (ρ) < (⌊(N + 1) / e⌋₊ + 1 - k) }) with
    | ⟨k', h1b⟩ => loop1 N e h_precond k' h1b.1
  else ⟨((k : ℚ) * e), by refine_auto⟩
termination_by ⌊(N + 1) / e⌋₊ + 1 - k
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h1b.2 | omega)


set_option maxHeartbeats 1000000 in
def sqrtApprox_derived (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond N e) : { ρ : ℚ // sqrtApprox_postcond N e ρ h_precond } :=
  (loop1 N e h_precond (0) (by refine_auto))

def sqrtApprox (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond N e) : ℚ := (sqrtApprox_derived N e h_precond).val

theorem sqrtApprox_spec_satisfied (N : ℚ) (e : ℚ) (h_precond : sqrtApprox_precond N e) :
    sqrtApprox_postcond N e (sqrtApprox N e h_precond) h_precond := (sqrtApprox_derived N e h_precond).property

#print axioms sqrtApprox_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((2 : ℚ)) ((1 / 10 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (7 / 5 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((2 : ℚ)) ((1 / 100 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (141 / 100 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((0 : ℚ)) ((1 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (0 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((9 : ℚ)) ((1 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (3 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((10 : ℚ)) ((1 / 2 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (3 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((1 / 4 : ℚ)) ((1 / 8 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (1 / 2 : ℚ)| ≤ (1 / 1000000 : ℚ))
set_option maxHeartbeats 2000000 in
#eval decide (|(sqrtApprox ((100 : ℚ)) ((3 : ℚ)) (by first | native_decide | trivial | (norm_num [sqrtApprox_precond]; done) | (simp [sqrtApprox_precond]; done) | decide | omega)) - (9 : ℚ)| ≤ (1 / 1000000 : ℚ))
