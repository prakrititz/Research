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
def xOrY_precond (n : Nat) (x : Int) (y : Int) : Prop :=
  True

@[reducible, simp] def primeSpec (n : Nat) : Prop := n ≥ 2 ∧ ∀ d, d < n → d ≥ 2 → n % d ≠ 0

@[reducible, simp]
def xOrY_postcond (n : Nat) (x : Int) (y : Int) (result: Int) (h_precond : xOrY_precond (n) (x) (y)) :=
  (primeSpec n → result = x) ∧ (¬ primeSpec n → result = y)



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))

def loop5 (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond n x y) (h2 : ¬ (n < 2)) (d : Nat) (ok : Bool) (h5i : (2 ≤ d ∧ d ≤ n ∧ (ok = true ↔ ∀ k, k < d → k ≥ 2 → n % k ≠ 0))) : { ρ : Bool // (fun (p : Bool) => p = true ↔ primeSpec n) ρ } :=
  if h5g : (d < n) then
    match (⟨((d + 1, ok && decide (n % d ≠ 0))), by refine_auto⟩ : { ρ : Nat × Bool // (fun (d : Nat) (ok : Bool) => 2 ≤ d ∧ d ≤ n ∧ (ok = true ↔ ∀ k, k < d → k ≥ 2 → n % k ≠ 0)) (ρ).1 (ρ).2 ∧ (fun (d : Nat) (ok : Bool) => n - d) (ρ).1 (ρ).2 < (n - d) }) with
    | ⟨(d', ok'), h5b⟩ => loop5 n x y h_precond h2 d' ok' h5b.1
  else ⟨(ok), by first | (have hEq : d = (n) := (by omega); subst hEq; refine_auto) | (refine_auto)⟩
termination_by n - d
decreasing_by
  all_goals (try simp_wf)
  all_goals (first | exact h5b.2 | omega)


set_option maxHeartbeats 1000000 in
def xOrY_derived (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond n x y) : { ρ : Int // xOrY_postcond n x y ρ h_precond } :=
  (match ((if h2 : (n < 2) then ⟨(false), by refine_auto⟩ else (loop5 n x y h_precond h2 (2) (true) (by refine_auto))) : { p : Bool // p = true ↔ primeSpec n }) with | ⟨p, h1⟩ => (if h3 : (p = true) then ⟨(x), by refine_auto⟩ else ⟨(y), by refine_auto⟩))

def xOrY (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond n x y) : Int := (xOrY_derived n x y h_precond).val

theorem xOrY_spec_satisfied (n : Nat) (x : Int) (y : Int) (h_precond : xOrY_precond n x y) :
    xOrY_postcond n x y (xOrY n x y h_precond) h_precond := (xOrY_derived n x y h_precond).property

#print axioms xOrY_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((xOrY (7) (34) (12) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (34))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (15) (8) (5) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (5))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (1259) (3) (52) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (3))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (91) (56) (129) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (129))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (6) (34) (1234) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (1234))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (1) (2) (0) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (0))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (2) (2) (0) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (2))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (0) (500) (1000) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (1000))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (31) (24) (22) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (24))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (55) (9) (9) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (9))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (48) (49) (-100) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == ((-100)))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (131) (130) (10) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (130))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (399) (-100) (2) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (2))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (1234) (56) (51) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (51))
set_option maxHeartbeats 2000000 in
#eval (((xOrY (1) (2) (1234) (by first | native_decide | trivial | (norm_num [xOrY_precond]; done) | (simp [xOrY_precond]; done) | decide | omega))) == (1234))
