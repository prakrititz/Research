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

def uniqChars (w : String) : Nat := w.toList.eraseDups.length

@[reducible, simp]
def findMax_precond (words : List String) : Prop :=
  True

@[reducible, simp]
def findMax_postcond (words : List String) (result: String) (h_precond : findMax_precond (words)) :=
  (words = [] ∧ result = "") ∨ (result ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars result) ∧ ∀ w ∈ words, uniqChars w = uniqChars result → ¬ (w < result))



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))

def loop4 (words : List String) (h_precond : findMax_precond words) (h1 : ¬ (words = [])) (k : Nat) (b : Nat) (h4i : (1 ≤ k ∧ k ≤ words.length ∧ b < k ∧ (∀ j, j < k → uniqChars words[j]! ≤ uniqChars words[b]!) ∧ ∀ j, j < k → uniqChars words[j]! = uniqChars words[b]! → ¬ (words[j]! < words[b]!))) : { ρ : String // (fun (m : String) => m ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars m) ∧ ∀ w ∈ words, uniqChars w = uniqChars m → ¬ (w < m)) ρ } :=
  if h4g : (k < words.length) then
    match (⟨((k + 1, if uniqChars words[k]! > uniqChars words[b]! ∨ (uniqChars words[k]! = uniqChars words[b]! ∧ words[k]! < words[b]!) then k else b)), by refine_auto⟩ : { ρ : Nat × Nat // (fun (k : Nat) (b : Nat) => 1 ≤ k ∧ k ≤ words.length ∧ b < k ∧ (∀ j, j < k → uniqChars words[j]! ≤ uniqChars words[b]!) ∧ ∀ j, j < k → uniqChars words[j]! = uniqChars words[b]! → ¬ (words[j]! < words[b]!)) (ρ).1 (ρ).2 ∧ (fun (k : Nat) (b : Nat) => words.length - k) (ρ).1 (ρ).2 < (words.length - k) }) with
    | ⟨(k', b'), h4b⟩ => loop4 words h_precond h1 k' b' h4b.1
  else ⟨(words[b]!), by first | (have hEq : k = (words.length) := (by omega); subst hEq; refine_auto) | (refine_auto)⟩
termination_by words.length - k
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h4b.2 | omega)


set_option maxHeartbeats 1000000 in
def findMax_derived (words : List String) (h_precond : findMax_precond words) : { ρ : String // findMax_postcond words ρ h_precond } :=
  (if h1 : (words = []) then ⟨(""), by refine_auto⟩ else (match ((loop4 words h_precond h1 (1) (0) (by refine_auto)) : { m : String // m ∈ words ∧ (∀ w ∈ words, uniqChars w ≤ uniqChars m) ∧ ∀ w ∈ words, uniqChars w = uniqChars m → ¬ (w < m) }) with | ⟨m, h3⟩ => ⟨(m), by refine_auto⟩))

def findMax (words : List String) (h_precond : findMax_precond words) : String := (findMax_derived words h_precond).val

theorem findMax_spec_satisfied (words : List String) (h_precond : findMax_precond words) :
    findMax_postcond words (findMax words h_precond) h_precond := (findMax_derived words h_precond).property

#print axioms findMax_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((findMax (["name", "of", "string"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("string"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["name", "enam", "game"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("enam"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["aaaaaaa", "bb", "cc"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("aaaaaaa"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["abc", "cba"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("abc"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["play", "this", "game", "of", "footbott"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("footbott"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["we", "are", "gonna", "rock"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("gonna"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["we", "are", "a", "mad", "nation"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("nation"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["this", "is", "a", "prrk"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("this"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["b"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("b"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["play", "play", "play"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("play"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["abacbdce", "edcbacba", "dbcaebda"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("abacbdce"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["abc", "bcd", "dbcaebda", "bbcd", "efg", "bbcd"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("dbcaebda"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["orange", "grape", "banana", "", "pear"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("orange"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["kiwi", "tac", "act", "r", "tac"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("act"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["xnyx", "hxfigy", "xyx", "zyx", "zyx", "xnyx"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("hxfigy"))
set_option maxHeartbeats 2000000 in
#eval (((findMax (["yx", "wyx", "yzyx"]) (by first | native_decide | trivial | (norm_num [findMax_precond]; done) | (simp [findMax_precond]; done) | decide | omega))) == ("wyx"))
