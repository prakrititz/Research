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
def isPalindrome_precond (text : String) : Prop :=
  True

@[reducible, simp]
def isPalindrome_postcond (text : String) (result: Bool) (h_precond : isPalindrome_precond (text)) :=
  result = true ↔ ∀ i, i < text.length → text.toList[i]! = text.toList[text.length - 1 - i]!



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))

def loop1 (text : String) (h_precond : isPalindrome_precond text) (i : Nat) (ok : Bool) (h1i : (i ≤ text.length ∧ (ok = true ↔ ∀ k, k < i → text.toList[k]! = text.toList[text.length - 1 - k]!))) : { ρ : Bool // isPalindrome_postcond text ρ h_precond } :=
  if h1g : (i < text.length) then
    match (⟨((i + 1, ok && decide (text.toList[i]! = text.toList[text.length - 1 - i]!))), by refine_auto⟩ : { ρ : Nat × Bool // (fun (i : Nat) (ok : Bool) => i ≤ text.length ∧ (ok = true ↔ ∀ k, k < i → text.toList[k]! = text.toList[text.length - 1 - k]!)) (ρ).1 (ρ).2 ∧ (fun (i : Nat) (ok : Bool) => text.length - i) (ρ).1 (ρ).2 < (text.length - i) }) with
    | ⟨(i', ok'), h1b⟩ => loop1 text h_precond i' ok' h1b.1
  else ⟨(ok), by first | (have hEq : i = (text.length) := (by omega); subst hEq; refine_auto) | (refine_auto)⟩
termination_by text.length - i
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h1b.2 | omega)


set_option maxHeartbeats 1000000 in
def isPalindrome_derived (text : String) (h_precond : isPalindrome_precond text) : { ρ : Bool // isPalindrome_postcond text ρ h_precond } :=
  (loop1 text h_precond (0) (true) (by refine_auto))

def isPalindrome (text : String) (h_precond : isPalindrome_precond text) : Bool := (isPalindrome_derived text h_precond).val

theorem isPalindrome_spec_satisfied (text : String) (h_precond : isPalindrome_precond text) :
    isPalindrome_postcond text (isPalindrome text h_precond) h_precond := (isPalindrome_derived text h_precond).property

#print axioms isPalindrome_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("aba") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("aaaaa") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("zbcd") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("xywyx") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("xywyz") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("xywzx") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("a") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("canal:") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("S") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (true))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("erecainWAsnral,Dd3!@@@2DoZz21o") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("petsesaw?n,") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("Do geese see Go") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("Step12zZ2petssaw@@@@!3j") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
set_option maxHeartbeats 2000000 in
#eval (((isPalindrome ("Panaanama.ma.") (by first | native_decide | trivial | (norm_num [isPalindrome_precond]; done) | (simp [isPalindrome_precond]; done) | decide | omega))) == (false))
