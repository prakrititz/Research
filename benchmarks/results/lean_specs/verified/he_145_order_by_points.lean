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

def digitWeight (x : Int) : Int :=
  let ds : List Nat := (toString x.natAbs).toList.map (fun c => c.toNat - 48)
  let s : Int := (ds.map (fun d => (d : Int))).sum
  if x < 0 then s - 2 * ((ds.head! : Nat) : Int) else s

@[reducible, simp]
def orderByPoints_precond (nums : List Int) : Prop :=
  True

@[reducible, simp]
def orderByPoints_postcond (nums : List Int) (result: List Int) (h_precond : orderByPoints_precond (nums)) :=
  result.length = nums.length ∧ (∀ i, i < result.length - 1 → digitWeight result[i]! ≤ digitWeight result[i + 1]!) ∧
    ∀ x ∈ nums, result.filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x)

set_option maxHeartbeats 400000 in
theorem order_ok : ∀ (nums : List Int), (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length = nums.length ∧ (∀ i, i < (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length - 1 → digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i]! ≤ digitWeight (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)))[i + 1]!) ∧ ∀ x ∈ nums, (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).filter (fun y => digitWeight y == digitWeight x) = nums.filter (fun y => digitWeight y == digitWeight x) := by
  intro nums
  have htrans : ∀ (a b c : Int), decide (digitWeight a ≤ digitWeight b) = true → decide (digitWeight b ≤ digitWeight c) = true →
      decide (digitWeight a ≤ digitWeight c) = true := by
    intro a b c h1 h2; simp at *; omega
  have htotal : ∀ (a b : Int), (decide (digitWeight a ≤ digitWeight b) || decide (digitWeight b ≤ digitWeight a)) = true := by
    intro a b; simp; omega
  have hp : (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).Perm nums := List.mergeSort_perm nums _
  have hs : List.Pairwise (fun a b => decide (digitWeight a ≤ digitWeight b) = true)
      (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))) := List.pairwise_mergeSort htrans htotal nums
  refine ⟨List.length_mergeSort .., ?_, ?_⟩
  · intro i hi
    rw [List.pairwise_iff_getElem] at hs
    have hi' : i + 1 < (nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))).length := by omega
    have := hs i (i + 1) (by omega) hi' (by omega)
    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']
    simpa using this
  · intro x hx
    set p : Int → Bool := fun y => digitWeight y == digitWeight x with hpdef
    set s := nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b)) with hsdef
    have hc : (nums.filter p).Pairwise (fun a b => decide (digitWeight a ≤ digitWeight b) = true) := by
      apply List.pairwise_of_forall_mem_list
      intro a ha b hb
      simp [hpdef] at ha hb
      simp; omega
    have hsub : (nums.filter p).Sublist s := List.sublist_mergeSort htrans htotal hc (List.filter_sublist)
    have hself : (nums.filter p).filter p = nums.filter p := by
      rw [List.filter_filter]; simp
    have hsub2 : (nums.filter p).Sublist (s.filter p) := by
      have := hsub.filter p
      rwa [hself] at this
    have hlen : (nums.filter p).length = (s.filter p).length := (List.Perm.filter p hp).length_eq.symm
    exact (hsub2.eq_of_length hlen).symm


macro "refine_auto" : tactic => `(tactic| (first | (apply order_ok; all_goals first | done | (simp_all; done) | omega | grind) | ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | (apply order_ok <;> simp_all) | (grind [order_ok]) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, order_ok] <;> grind [order_ok]) | nlinarith | (aesop; done)))))


set_option maxHeartbeats 1000000 in
def orderByPoints_derived (nums : List Int) (h_precond : orderByPoints_precond nums) : { ρ : List Int // orderByPoints_postcond nums ρ h_precond } :=
  ⟨(nums.mergeSort (fun a b => decide (digitWeight a ≤ digitWeight b))), by refine_auto⟩

def orderByPoints (nums : List Int) (h_precond : orderByPoints_precond nums) : List Int := (orderByPoints_derived nums h_precond).val

theorem orderByPoints_spec_satisfied (nums : List Int) (h_precond : orderByPoints_precond nums) :
    orderByPoints_postcond nums (orderByPoints nums h_precond) h_precond := (orderByPoints_derived nums h_precond).property

#print axioms orderByPoints_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, 11, -1, -11, -12]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-1, -11, 1, -12, 11]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, -11, -32, 43, 54, -98, 2, -3]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-3, -32, -98, -11, 1, 2, 43, 54]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([1, 10, 2, 11, 3, 4, 5, 6, 7, 8, 9]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([0, 6, 6, -76, -21, 23, 4]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-76, -21, 0, 4, 23, 6, 6]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, 2, 3]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([1, 2, 3]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([-753, 824, -444, 222, 824]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-753, -444, 222, 824, 824]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([4444]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([4444]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([27, -89, -54, 63, -72, 667, -90, 63]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-90, -72, -54, -89, 27, 63, 63, 667]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, 2, 3, -753, 1]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([1, -753, 1, 2, 3]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([86, -345, -1000, 200, -200, 500, -500, 333, -333, 500]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-500, -200, -1000, 200, -333, 500, 500, -345, 333, 86]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([21, 31, 38, -204, -206, 213, 161, -900, 915, 53, -901, -39, -808]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-900, -901, -808, -204, 21, 31, -206, 213, -39, 161, 53, 38, 915]))
set_option maxHeartbeats 2000000 in
#eval (((orderByPoints ([1, -22, -43, -35, -57, -98, 79, -11, 0, 6, 13, -38, 0]) (by first | native_decide | trivial | (norm_num [orderByPoints_precond]; done) | (simp [orderByPoints_precond]; done) | decide | omega))) == ([-43, -98, -22, -11, 0, 0, 1, -35, -57, 13, -38, 6, 79]))
