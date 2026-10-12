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

def md5K : Array UInt32 := #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]
def md5S : Array UInt32 := #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]
def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n]!
def md5Pad (msg : List UInt8) : List UInt8 :=
  let l := msg.length
  msg ++ [0x80] ++ List.replicate ((55 + 64 - l % 64) % 64) 0 ++ (List.range 8).map (fun i => UInt8.ofNat ((l * 8 / 256 ^ i) % 256))
def md5Word (blk : List UInt8) (j : Nat) : UInt32 :=
  blk[4 * j]!.toUInt32 ||| (blk[4 * j + 1]!.toUInt32 <<< 8) ||| (blk[4 * j + 2]!.toUInt32 <<< 16) ||| (blk[4 * j + 3]!.toUInt32 <<< 24)
def md5Step (m : Array UInt32) (st : UInt32 × UInt32 × UInt32 × UInt32) (i : Nat) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := st.1
  let b := st.2.1
  let c := st.2.2.1
  let d := st.2.2.2
  let fg : UInt32 × Nat :=
    if i < 16 then ((b &&& c) ||| ((~~~b) &&& d), i)
    else if i < 32 then ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
    else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
    else (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
  let f := fg.1 + a + md5K[i]! + m[fg.2]!
  let s := md5S[i]!
  (d, b + ((f <<< s) ||| (f >>> (32 - s))), b, c)
def md5Block (st : UInt32 × UInt32 × UInt32 × UInt32) (blk : List UInt8) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let m : Array UInt32 := ((List.range 16).map (md5Word blk)).toArray
  let r := (List.range 64).foldl (md5Step m) st
  (st.1 + r.1, st.2.1 + r.2.1, st.2.2.1 + r.2.2.1, st.2.2.2 + r.2.2.2)
def md5Blocks : Nat → List UInt8 → UInt32 × UInt32 × UInt32 × UInt32 → UInt32 × UInt32 × UInt32 × UInt32
  | 0, _, st => st
  | fuel + 1, bytes, st => if bytes.length < 64 then st else md5Blocks fuel (bytes.drop 64) (md5Block st (bytes.take 64))
def md5Hex (s : String) : String :=
  let bytes := md5Pad s.toUTF8.toList
  let st := md5Blocks bytes.length bytes (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476)
  let out := [st.1, st.2.1, st.2.2.1, st.2.2.2].flatMap (fun w => (List.range 4).map (fun k => ((w >>> (8 * k).toUInt32) &&& 0xff).toNat))
  String.mk (out.flatMap (fun b => [hexDigit (b / 16), hexDigit (b % 16)]))

@[reducible, simp]
def stringToMd5_precond (text : String) : Prop :=
  True

@[reducible, simp]
def stringToMd5_postcond (text : String) (result: Option String) (h_precond : stringToMd5_precond (text)) :=
  (text = "" → result = none) ∧ (text ≠ "" → result = some (md5Hex text))



macro "refine_auto" : tactic => `(tactic| ((try dsimp only at *); (repeat' apply And.intro); all_goals (first | omega | grind | (simp_all; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; omega) | (simp_all; omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm]; done) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, mul_assoc]; done) | (split <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem]; done) | (split_ifs <;> simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem] <;> omega) | (simp_all [Refine.forall_mem_iff_idx, Refine.exists_mem_iff_idx, Refine.getElem_bang_mem, Refine.getElem_bang_mem_take, Refine.head_mem_take_one, Refine.take_succ_bang, Refine.sum_take_succ_bang, Refine.head_bang_eq, Refine.getElem_bang_append_lt, Refine.getElem_bang_append_length, Refine.exists_le_succ, Refine.forall_le_succ, Refine.take_string_length, Refine.forall_mem_toList_iff_idx, Refine.exists_mem_toList_iff_idx, Refine.forall_mem_array_iff_idx, Refine.exists_mem_array_iff_idx, String.length_toList, List.range_succ, -List.take_append_getElem, Nat.mul_comm, Nat.mul_left_comm]; done) | (rw [Refine.forall_mem_iff_idx]; grind) | (rw [Refine.exists_mem_iff_idx]; grind) | nlinarith | (aesop; done))))


set_option maxHeartbeats 1000000 in
def stringToMd5_derived (text : String) (h_precond : stringToMd5_precond text) : { ρ : Option String // stringToMd5_postcond text ρ h_precond } :=
  (if h1 : (text = "") then ⟨(none), by refine_auto⟩ else ⟨(some (md5Hex text)), by refine_auto⟩)

def stringToMd5 (text : String) (h_precond : stringToMd5_precond text) : Option String := (stringToMd5_derived text h_precond).val

theorem stringToMd5_spec_satisfied (text : String) (h_precond : stringToMd5_precond text) :
    stringToMd5_postcond text (stringToMd5 text h_precond) h_precond := (stringToMd5_derived text h_precond).property

#print axioms stringToMd5_spec_satisfied

set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("Hello world") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("3e25960a79dbc69b674cd4ec67a72c62")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (none))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("A B C") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("0ef78513b0cb8cef12743f5aeb35f888")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("password") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("5f4dcc3b5aa765d61d8327deb882cf99")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("5873hajsdklh") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("0dbb501bb9d84c751d2cf6394d9308c0")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("you_are_beautiful_t0day!123") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("1a968aa5e9ec50a5659ae74027b76e65")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("mattisi,") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("a83b94f8f37c84bf2ac6d0d9d37b9e22")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("nfordshouldon-triinnpptvialtt") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("dc3489f74acab5d5336362f9b429fb1e")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("elLorem") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("d04ce2b6ea61622d94716c1f2845f84f")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("et") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("4de1b7a4dc53e4a84c25ffb7cdb580ee")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("lolonNunclreme") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("1c89d79751e5c6b7bceb1dc78035cb22")))
set_option maxHeartbeats 2000000 in
#eval (((stringToMd5 ("fox") (by first | native_decide | trivial | (norm_num [stringToMd5_precond]; done) | (simp [stringToMd5_precond]; done) | decide | omega))) == (some ("2b95d1f09b8b66c5c43622a4d9ec9a04")))
