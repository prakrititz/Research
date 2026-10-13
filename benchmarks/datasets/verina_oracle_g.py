r"""Hand-written derivations for Verina tasks, batch G (the remaining basic family: searches, builders, closed forms)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_b import _builder

_STEP43 = {
    "name": "step43",
    "statement": "∀ (i acc : Nat), 15*acc = i*(2*i+1)*(7+24*i^3-12*i^2-14*i) → "
                 "15*(acc + (2*i+1)^4) = (i+1)*(2*(i+1)+1)*(7+24*(i+1)^3-12*(i+1)^2-14*(i+1))",
    "proof": "by intro i acc h\n"
             "  have key : ∀ j : Nat, 12*j^2+14*j ≤ 7+24*j^3 := by\n    intro j; rcases j with _|j\n    · simp\n    · ring_nf; omega\n"
             "  have e : ∀ j : Nat, ((7+24*j^3-12*j^2-14*j : Nat) : Int) = 7+24*(j:Int)^3-12*(j:Int)^2-14*(j:Int) := by\n"
             "    intro j\n    have := key j\n    have h1 : 12*j^2 ≤ 7+24*j^3 := by omega\n"
             "    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]; push_cast; ring\n"
             "  have hz : (15:Int)*acc = i*(2*i+1)*(7+24*(i:Int)^3-12*(i:Int)^2-14*(i:Int)) := by\n"
             "    have := congrArg (fun x : Nat => (x : Int)) h\n    simp only [Nat.cast_mul, Nat.cast_ofNat, e] at this\n"
             "    push_cast at this\n    exact this\n"
             "  have goal : ((15*(acc + (2*i+1)^4) : Nat) : Int) = (((i+1)*(2*(i+1)+1)*(7+24*(i+1)^3-12*(i+1)^2-14*(i+1)) : Nat) : Int) := by\n"
             "    have e1 := e (i+1)\n    push_cast at e1 ⊢\n    rw [e1]\n    push_cast\n    nlinarith [hz]\n"
             "  exact_mod_cast goal"}

_STEP7 = {
    "name": "step7",
    "statement": "∀ (i acc : Nat), 3*acc = i*(2*i-1)*(2*i+1) → 3*(acc + (2*i+1)*(2*i+1)) = (i+1)*(2*(i+1)-1)*(2*(i+1)+1)",
    "proof": "by intro i acc h\n  rcases i with _|i\n  · simp at h ⊢; omega\n"
             "  · have e1 : 2*(i+1)-1 = 2*i+1 := by omega\n    have e2 : 2*(i+1+1)-1 = 2*i+3 := by omega\n"
             "    rw [e1] at h; rw [e2]\n    nlinarith [h]"}

_EXIT46 = {
    "name": "exit46",
    "statement": "∀ (arr : Array Int) (elem : Int) (i : Nat) (pos : Int) (h : lastPosition_precond arr elem), "
                 "(i ≤ arr.size ∧ (pos = -1 ∨ (0 ≤ pos ∧ pos.toNat < i ∧ arr[pos.toNat]! = elem)) ∧ "
                 "(pos = -1 → ∀ k, k < i → arr[k]! ≠ elem) ∧ (0 ≤ pos → ∀ k, pos.toNat < k → k < i → arr[k]! ≠ elem)) → "
                 "¬ i < arr.size → lastPosition_postcond arr elem pos h",
    "proof": "by intro arr elem i pos h hinv hn\n  obtain ⟨hi, hp, h1, h2⟩ := hinv\n"
             "  have hi' : i = arr.size := by omega\n  subst hi'\n  unfold lastPosition_postcond\n  refine ⟨?_, ?_, ?_⟩\n"
             "  · rcases hp with hp | hp\n    · left; exact hp\n    · right; omega\n"
             "  · intro hge\n    rcases hp with hp | ⟨_, hb, he⟩\n    · omega\n"
             "    · refine ⟨hb, he, ?_⟩\n      simp only [List.all_eq_true, decide_eq_true_eq]\n"
             "      rw [Refine.forall_mem_drop_iff]\n      intro k hk1 hk2\n"
             "      have hk2' : k < arr.size := by simpa using hk2\n"
             "      rw [Refine.toList_getElem_bang arr k hk2']\n      exact h2 (by omega) k (by omega) hk2'\n"
             "  · intro hneg\n    simp only [List.all_eq_true, decide_eq_true_eq]\n"
             "    rw [Refine.forall_mem_toList_iff_idx]\n    intro k hk\n    exact h1 hneg k hk"}

_EXIT51 = {
    "name": "exit51",
    "statement": "∀ (a : Array Int) (key : Int) (i : Nat) (h : BinarySearch_precond a key), "
                 "(i ≤ a.size ∧ ∀ k, k < i → a[k]! < key) → ¬ (i < a.size ∧ a[i]! < key) → BinarySearch_postcond a key i h",
    "proof": "by intro a key i h hinv hn\n  obtain ⟨hi, hk⟩ := hinv\n  have hs := Refine.sorted_arr_le a h\n"
             "  unfold BinarySearch_postcond\n  refine ⟨hi, ?_, ?_⟩\n"
             "  · rw [Refine.arr_all_take_iff]; intro k hk1 _; simpa using hk k hk1\n"
             "  · rw [Refine.arr_all_drop_iff]; intro k hk1 hk2\n"
             "    have hlt : i < a.size := by omega\n    have h1 : ¬ a[i]! < key := fun hx => hn ⟨hlt, hx⟩\n"
             "    have h2 := hs i k hk1 hk2\n    simp only [decide_eq_true_eq]; omega"}

_EXIT60 = {
    "name": "exit60",
    "statement": "∀ (arr acc : Array Int) (i : Nat) (h : FindEvenNumbers_precond arr), "
                 "(i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven) → ¬ i < arr.size → FindEvenNumbers_postcond arr acc h",
    "proof": "by intro arr acc i h hinv hn\n  obtain ⟨hi, hacc⟩ := hinv\n  have hi' : i = arr.size := by omega\n  subst hi'\n"
             "  have ht : arr.toList.take arr.size = arr.toList := List.take_of_length_le (by simp)\n  rw [ht] at hacc\n"
             "  unfold FindEvenNumbers_postcond\n  refine ⟨?_, ?_, ?_⟩\n"
             "  · rw [← Array.all_toList, hacc, List.all_eq_true]\n    intro x hx; exact (List.mem_filter.mp hx).2\n"
             "  · rw [hacc]; exact List.filter_sublist\n"
             "  · rw [← Array.length_toList, hacc, List.countP_eq_length_filter]"}

_EXIT54 = {
    "name": "exit54",
    "statement": "∀ (a b : Array Int) (i best : Nat) (h : CanyonSearch_precond a b), "
                 "(i ≤ a.size ∧ (∃ ii, ii < a.size ∧ ∃ jj, jj < b.size ∧ best = (a[ii]! - b[jj]!).natAbs) ∧ "
                 "∀ k, k < i → ∀ j, j < b.size → best ≤ (a[k]! - b[j]!).natAbs) → ¬ i < a.size → CanyonSearch_postcond a b best h",
    "proof": "by intro a b i best h hinv hn\n  obtain ⟨hi, ⟨ii, hii, jj, hjj, hb⟩, hall⟩ := hinv\n"
             "  have hi' : i = a.size := by omega\n  subst hi'\n  unfold CanyonSearch_postcond\n  constructor\n"
             "  · rw [← Array.any_toList, List.any_eq_true]\n    refine ⟨a[ii]!, ?_, ?_⟩\n"
             "    · rw [← Refine.toList_getElem_bang a ii hii]; exact Refine.getElem_bang_mem _ _ (by simpa using hii)\n"
             "    · rw [← Array.any_toList, List.any_eq_true]\n      refine ⟨b[jj]!, ?_, by simpa using hb⟩\n"
             "      rw [← Refine.toList_getElem_bang b jj hjj]; exact Refine.getElem_bang_mem _ _ (by simpa using hjj)\n"
             "  · rw [← Array.all_toList, List.all_eq_true, Refine.forall_mem_toList_iff_idx]\n    intro k hk\n"
             "    rw [← Array.all_toList, List.all_eq_true, Refine.forall_mem_toList_iff_idx]\n    intro j hj\n"
             "    simpa using hall k hk j hj"}

_EXIT40 = {
    "name": "exit40",
    "statement": "∀ (s : Array Int) (m r : Int) (found : Bool) (i : Nat) (h : secondSmallest_precond s), "
                 "((∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!) → "
                 "(i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ "
                 "(found = false → ∀ k, k < i → s[k]! = m)) → ¬ i < s.size → secondSmallest_postcond s r h",
    "proof": "by intro s m r found i h hm hinv hn\n  obtain ⟨⟨idx, hidx, hmi⟩, hmin⟩ := hm\n  obtain ⟨hi, ht, hf⟩ := hinv\n"
             "  have hi' : i = s.size := by omega\n  subst hi'\n"
             "  have hfound : found = true := by\n    by_contra hne\n    have hf' : found = false := by simpa using hne\n"
             "    have hall := hf hf'\n    obtain ⟨_, p, q, _, _, hpq⟩ := h\n"
             "    exact hpq (by rw [hall p ‹p < s.size›, hall q ‹q < s.size›])\n"
             "  obtain ⟨⟨j, hj, hsj⟩, hmr, hle⟩ := ht hfound\n"
             "  unfold secondSmallest_postcond\n  refine ⟨⟨j, hj, hsj⟩, idx, hidx, by omega, ?_⟩\n"
             "  intro k hk hne\n  have h1 := hmin k hk\n  have : m < s[k]! := by omega\n  exact hle k hk this"}

_STEP40 = {
    "name": "step40",
    "statement": "∀ (s : Array Int) (m r : Int) (found : Bool) (i : Nat), "
                 "((∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!) → i < s.size → "
                 "(i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ "
                 "(found = false → ∀ k, k < i → s[k]! = m)) → "
                 "(i + 1 ≤ s.size ∧ ((if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found) = true → "
                 "(∃ idx, idx < i + 1 ∧ s[idx]! = (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r)) ∧ "
                 "m < (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r) ∧ "
                 "∀ k, k < i + 1 → m < s[k]! → (if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r) ≤ s[k]!) ∧ "
                 "((if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found) = false → ∀ k, k < i + 1 → s[k]! = m))",
    "proof": "by intro s m r found i hm hi hinv\n  obtain ⟨hle, ht, hf⟩ := hinv\n  have hmin := hm.2\n"
             "  by_cases hc : m < s[i]! ∧ (found = false ∨ s[i]! < r)\n"
             "  · rw [if_pos hc, if_pos hc]\n    have hmi := hc.1\n"
             "    refine ⟨by omega, fun _ => ⟨⟨i, by omega, rfl⟩, hmi, ?_⟩, fun h => by simp at h⟩\n"
             "    intro k hk hmk\n    by_cases hk' : k = i\n    · subst hk'; exact le_refl _\n"
             "    · have hkl : k < i := by omega\n      by_cases hfd : found = true\n"
             "      · have := (ht hfd).2.2 k hkl hmk\n        rcases hc.2 with h0 | h0\n"
             "        · rw [hfd] at h0; simp at h0\n        · omega\n"
             "      · have hf0 : found = false := by simpa using hfd\n        have := hf hf0 k hkl; omega\n"
             "  · rw [if_neg hc, if_neg hc]\n    refine ⟨by omega, ?_, ?_⟩\n"
             "    · intro hfd\n      obtain ⟨⟨idx, hidx, hv⟩, hmr, hle'⟩ := ht hfd\n"
             "      refine ⟨⟨idx, by omega, hv⟩, hmr, ?_⟩\n      intro k hk hmk\n      by_cases hk' : k = i\n"
             "      · rw [hk'] at hmk ⊢\n        by_contra hcon\n        exact hc ⟨hmk, Or.inr (by omega)⟩\n"
             "      · exact hle' k (by omega) hmk\n"
             "    · intro hf0 k hk\n      by_cases hk' : k = i\n"
             "      · rw [hk']\n        have := hmin i hi\n        by_contra hcon\n        exact hc ⟨by omega, Or.inl hf0⟩\n"
             "      · exact hf hf0 k (by omega)"}

_STEP71 = {
    "name": "step71",
    "statement": "∀ (l1 l2 : List Char) (idx : Nat), (idx ≤ min l1.length l2.length ∧ l1.take idx = l2.take idx) → "
                 "(idx < min l1.length l2.length ∧ l1[idx]! = l2[idx]!) → "
                 "(idx + 1 ≤ min l1.length l2.length ∧ l1.take (idx + 1) = l2.take (idx + 1))",
    "proof": "by intro l1 l2 idx ⟨_, h⟩ ⟨hl, he⟩\n  have h1 : idx < l1.length := by omega\n  have h2 : idx < l2.length := by omega\n"
             "  refine ⟨by omega, ?_⟩\n  rw [Refine.take_succ_bang l1 idx h1, Refine.take_succ_bang l2 idx h2, h, he]"}

ORACLES_MORE = {
    "verina_basic_46": with_lemmas(
        loop([["i", "Nat"], ["pos", "Int"]], ["0", "-1"],
             "i ≤ arr.size ∧ (pos = -1 ∨ (0 ≤ pos ∧ pos.toNat < i ∧ arr[pos.toNat]! = elem)) ∧ "
             "(pos = -1 → ∀ k, k < i → arr[k]! ≠ elem) ∧ (0 ≤ pos → ∀ k, pos.toNat < k → k < i → arr[k]! ≠ elem)",
             "i < arr.size", "arr.size - i", "pos",
             term("(i + 1, if arr[i]! = elem then (i : Int) else pos)")), [_EXIT46]),
    "verina_basic_40": with_lemmas(
        bind("m", "Int", "(∃ idx, idx < s.size ∧ s[idx]! = m) ∧ ∀ k, k < s.size → m ≤ s[k]!",
             loop([["i", "Nat"], ["m", "Int"]], ["1", "s[0]!"],
                  "1 ≤ i ∧ i ≤ s.size ∧ (∃ idx, idx < i ∧ s[idx]! = m) ∧ ∀ k, k < i → m ≤ s[k]!",
                  "i < s.size", "s.size - i", "m", term("(i + 1, min m s[i]!)")),
             loop([["i", "Nat"], ["r", "Int"], ["found", "Bool"]], ["0", "0", "false"],
                  "i ≤ s.size ∧ (found = true → (∃ idx, idx < i ∧ s[idx]! = r) ∧ m < r ∧ ∀ k, k < i → m < s[k]! → r ≤ s[k]!) ∧ "
                  "(found = false → ∀ k, k < i → s[k]! = m)",
                  "i < s.size", "s.size - i", "r",
                  term("(i + 1, if m < s[i]! ∧ (found = false ∨ s[i]! < r) then s[i]! else r, "
                       "if m < s[i]! ∧ (found = false ∨ s[i]! < r) then true else found)"))), [_EXIT40, _STEP40]),
    "verina_basic_60": with_lemmas(
        loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
             "i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven",
             "i < arr.size", "arr.size - i", "acc",
             term("(i + 1, if isEven arr[i]! then acc.push arr[i]! else acc)")), [_EXIT60]),
    "verina_basic_51": with_lemmas(
        loop([["i", "Nat"]], ["0"], "i ≤ a.size ∧ ∀ k, k < i → a[k]! < key", "i < a.size ∧ a[i]! < key",
             "a.size - i", "i", term("i + 1")), [_EXIT51]),
    "verina_basic_54": with_lemmas(
        loop([["i", "Nat"], ["best", "Nat"]], ["0", "(a[0]! - b[0]!).natAbs"],
             "i ≤ a.size ∧ (∃ ii, ii < a.size ∧ ∃ jj, jj < b.size ∧ best = (a[ii]! - b[jj]!).natAbs) ∧ "
             "∀ k, k < i → ∀ j, j < b.size → best ≤ (a[k]! - b[j]!).natAbs",
             "i < a.size", "a.size - i", "best",
             bind("row", "Nat", "(∃ jj, jj < b.size ∧ row = (a[i]! - b[jj]!).natAbs) ∧ ∀ jj, jj < b.size → row ≤ (a[i]! - b[jj]!).natAbs",
                  loop([["j", "Nat"], ["row", "Nat"]], ["1", "(a[i]! - b[0]!).natAbs"],
                       "1 ≤ j ∧ j ≤ b.size ∧ (∃ jj, jj < j ∧ row = (a[i]! - b[jj]!).natAbs) ∧ ∀ jj, jj < j → row ≤ (a[i]! - b[jj]!).natAbs",
                       "j < b.size", "b.size - j", "row", term("(j + 1, min row (a[i]! - b[j]!).natAbs)")),
                  term("(i + 1, min best row)"))), [_EXIT54]),
    "verina_basic_7": with_lemmas(
        loop([["i", "Nat"], ["acc", "Nat"]], ["0", "0"], "i ≤ n ∧ 3 * acc = i * (2 * i - 1) * (2 * i + 1)",
             "i < n", "n - i", "acc", term("(i + 1, acc + (2 * i + 1) * (2 * i + 1))")), [_STEP7]),
    "verina_basic_43": with_lemmas(
        loop([["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
             "i ≤ n ∧ 15 * acc = i * (2 * i + 1) * (7 + 24 * i^3 - 12 * i^2 - 14 * i)",
             "i < n", "n - i", "acc", term("(i + 1, acc + (2 * i + 1)^4)")), [_STEP43]),
    "verina_basic_29": _builder("s", "(if IDX < k then s[IDX]! else s[IDX + 1]!)", "s.size - 1"),
    "verina_basic_64": loop([["i", "Nat"], ["acc", "Array Char"]], ["0", "#[]"],
                            "i ≤ l + p ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = "
                            "(if jj < atPos then oline[jj]! else if jj < atPos + p then nl[jj - atPos]! else oline[jj - p]!)",
                            "i < l + p", "l + p - i", "acc",
                            term("(i + 1, acc.push (if i < atPos then oline[i]! else if i < atPos + p then nl[i - atPos]! else oline[i - p]!))")),
    "verina_basic_71": with_lemmas(
        loop([["idx", "Nat"]], ["0"], "idx ≤ min str1.length str2.length ∧ str1.take idx = str2.take idx",
             "idx < min str1.length str2.length ∧ str1[idx]! = str2[idx]!",
             "min str1.length str2.length - idx", "str1.take idx", term("idx + 1")), [_STEP71]),
}
