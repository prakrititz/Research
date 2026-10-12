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
def fileNameCheck_precond (file_name : String) : Prop :=
  True

@[reducible, simp]
def fileNameCheck_postcond (file_name : String) (result: String) (h_precond : fileNameCheck_precond (file_name)) :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧
    ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧
      (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)))



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))


set_option maxHeartbeats 1000000 in
def fileNameCheck_derived (file_name : String) (h_precond : fileNameCheck_precond file_name) : { ρ : String // fileNameCheck_postcond file_name ρ h_precond } :=
  (if h1 : ((file_name.toList.filter Char.isDigit).length ≤ 3 ∧ file_name.toList.count '.' = 1 ∧ ∃ i, i < file_name.length ∧ file_name.toList[i]! = '.' ∧ 0 < i ∧ file_name.toList[0]!.isAlpha = true ∧ (file_name.toList.drop (i + 1) = "txt".toList ∨ file_name.toList.drop (i + 1) = "exe".toList ∨ file_name.toList.drop (i + 1) = "dll".toList)) then ⟨("Yes"), by refine_auto⟩ else ⟨("No"), by refine_auto⟩)

def fileNameCheck (file_name : String) (h_precond : fileNameCheck_precond file_name) : String := (fileNameCheck_derived file_name h_precond).val

theorem fileNameCheck_spec_satisfied (file_name : String) (h_precond : fileNameCheck_precond file_name) :
    fileNameCheck_postcond file_name (fileNameCheck file_name h_precond) h_precond := (fileNameCheck_derived file_name h_precond).property

#print axioms fileNameCheck_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("example.txt") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("Yes"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("1example.dll") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("s1sdf3.asd") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("K.dll") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("Yes"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("MY16FILE3.exe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("Yes"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("His12FILE94.exe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("_Y.txt") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("?aREYA.exe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("/this_is_valid.dll") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("this_is_valid.wow") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("this_is_valid.txt") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("Yes"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("this_is_valid.txtexe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("#this2_i4s_5valid.ten") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("@this1_is6_valid.exe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("all.exe.txt") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("No"))
set_option maxHeartbeats 2000000 in
#eval (((fileNameCheck ("I563_No.exe") (by first | native_decide | trivial | (norm_num [fileNameCheck_precond]; done) | (simp [fileNameCheck_precond]; done) | decide | omega))) == ("Yes"))
