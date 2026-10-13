r"""Hand-written derivations for Verina tasks, batch H (basic: filters, rotations, segment copies, running sums)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_MZ = {
    "name": "moveZeroes_ok",
    "statement": "∀ (arr : Array Int) (h : MoveZeroesToEnd_precond arr), MoveZeroesToEnd_postcond arr "
                 "(Array.mk (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0))) h",
    "proof": "by intro arr h\n  unfold MoveZeroesToEnd_postcond\n"
             "  have hF : (0 : Int) ∉ arr.toList.filter (· ≠ 0) := by simp\n"
             "  have hZ : (arr.toList.filter (· = 0)).idxOf 0 = 0 := by\n"
             "    rcases hz : arr.toList.filter (· = 0) with _ | ⟨x, t⟩\n    · rw [hz]; simp\n"
             "    · have : x = 0 := by\n        have : x ∈ arr.toList.filter (· = 0) := by rw [hz]; simp\n"
             "        simpa using (List.mem_filter.mp this).2\n      rw [hz, this]; simp\n"
             "  have hi : (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0)).idxOf 0 = (arr.toList.filter (· ≠ 0)).length := by\n"
             "    rw [List.idxOf_append_of_notMem hF, hZ]; simp\n"
             "  dsimp only\n  rw [hi]\n  refine ⟨?_, ?_, ?_⟩\n"
             "  · rw [List.isPerm_iff]\n    have := List.filter_append_perm (fun x : Int => decide (x ≠ 0)) arr.toList\n    simpa using this\n"
             "  · exact List.take_left' rfl\n  · exact List.drop_left' rfl"}

_ROT = {
    "name": "rotate_ok",
    "statement": "∀ (l : List Int) (n : Nat) (h : rotateRight_precond l n), l.length ≠ 0 → rotateRight_postcond l n "
                 "((List.range l.length).map (fun i : Nat => l.getD (Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % "
                 "Int.ofNat l.length)) (l.headD 0))) h",
    "proof": "by intro l n h hne\n  unfold rotateRight_postcond\n  refine ⟨by simp, ?_⟩\n  intro i hi\n"
             "  have hidx : Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % Int.ofNat l.length) < l.length := by\n"
             "    simp only [Int.ofNat_eq_natCast]\n"
             "    have h1 := Int.emod_lt_of_pos ((i : Int) - (n : Int) + (l.length : Int)) (by omega : (0:Int) < (l.length : Int))\n"
             "    have h0 := Int.emod_nonneg ((i : Int) - (n : Int) + (l.length : Int)) (by omega : (l.length : Int) ≠ 0)\n"
             "    omega\n"
             "  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]\n"
             "  rw [List.getD_eq_getElem _ _ hidx, List.getElem?_eq_getElem hidx]"}

_SETGET = {
    "name": "set_bang_get",
    "statement": "∀ (r : Array Int) (p : Nat) (v : Int) (k : Nat), p < r.size → (r.set! p v)[k]! = if p = k then v else r[k]!",
    "proof": "by intro r p v k hp\n  rw [Array.set!_eq_setIfInBounds]\n  by_cases hk : k < r.size\n"
             "  · have hk' : k < (r.setIfInBounds p v).size := by simpa using hk\n"
             "    rw [getElem!_pos (r.setIfInBounds p v) k hk', getElem!_pos r k hk, Array.getElem_setIfInBounds hk]\n"
             "  · have h1 : ¬ k < (r.setIfInBounds p v).size := by simpa using hk\n"
             "    rw [getElem!_neg (r.setIfInBounds p v) k h1, getElem!_neg r k hk]\n    split\n    · omega\n    · rfl"}

_INV56 = ("i ≤ len ∧ r.size = dest.size ∧ (∀ k, k < dStart → r[k]! = dest[k]!) ∧ "
          "(∀ k, dStart + i ≤ k → k < r.size → r[k]! = dest[k]!) ∧ (∀ k, k < i → r[dStart + k]! = src[sStart + k]!)")
_STEP56 = {
    "name": "step56",
    "statement": "∀ (src dest r : Array Int) (sStart dStart len i : Nat), copy_precond src sStart dest dStart len → i < len → "
                 "(i ≤ len ∧ r.size = dest.size ∧ (∀ k, k < dStart → r[k]! = dest[k]!) ∧ "
                 "(∀ k, dStart + i ≤ k → k < r.size → r[k]! = dest[k]!) ∧ (∀ k, k < i → r[dStart + k]! = src[sStart + k]!)) → "
                 "(i + 1 ≤ len ∧ (r.set! (dStart + i) src[sStart + i]!).size = dest.size ∧ "
                 "(∀ k, k < dStart → (r.set! (dStart + i) src[sStart + i]!)[k]! = dest[k]!) ∧ "
                 "(∀ k, dStart + (i + 1) ≤ k → k < (r.set! (dStart + i) src[sStart + i]!).size → "
                 "(r.set! (dStart + i) src[sStart + i]!)[k]! = dest[k]!) ∧ "
                 "(∀ k, k < i + 1 → (r.set! (dStart + i) src[sStart + i]!)[dStart + k]! = src[sStart + k]!))",
    "proof": "by intro src dest r sStart dStart len i hpre hi hinv\n  obtain ⟨h1, h2⟩ := hpre\n  obtain ⟨_, hs, ha, hb, hc⟩ := hinv\n"
             "  have hp : dStart + i < r.size := by omega\n"
             "  have hsz : (r.set! (dStart + i) src[sStart + i]!).size = r.size := Array.size_set! _ _ _\n"
             "  refine ⟨by omega, by rw [hsz]; exact hs, ?_, ?_, ?_⟩\n"
             "  · intro k hk\n    rw [set_bang_get r _ _ k hp, if_neg (by omega)]; exact ha k hk\n"
             "  · intro k hk hk2\n    rw [hsz] at hk2\n    rw [set_bang_get r _ _ k hp, if_neg (by omega)]; exact hb k (by omega) hk2\n"
             "  · intro k hk\n    rw [set_bang_get r _ _ _ hp]\n    by_cases hki : k = i\n    · subst hki; simp\n"
             "    · rw [if_neg (by omega)]; exact hc k (by omega)"}
_EXIT56 = {
    "name": "exit56",
    "statement": "∀ (src dest r : Array Int) (sStart dStart len i : Nat) (h : copy_precond src sStart dest dStart len), "
                 f"({_INV56}) → ¬ i < len → copy_postcond src sStart dest dStart len r h",
    "proof": "by intro src dest r sStart dStart len i h hinv hn\n  obtain ⟨hi, hs, ha, hb, hc⟩ := hinv\n"
             "  have hi' : i = len := by omega\n  subst hi'\n  unfold copy_postcond\n  exact ⟨hs, ha, hb, hc⟩"}

_EXIT108 = {
    "name": "exit108",
    "statement": "∀ (ops : List Int) (s : Array Int) (h : below_zero_precond ops), "
                 "(s.size = ops.length + 1 ∧ s[0]! = 0 ∧ ∀ i, i < ops.length → s[i+1]! = s[i]! + ops[i]!) → "
                 "below_zero_postcond ops (s, (List.range ops.length).any (fun i => decide (s[i+1]! < 0))) h",
    "proof": "by intro ops s h hp\n  obtain ⟨hs, h0, hstep⟩ := hp\n  unfold below_zero_postcond\n  dsimp only\n"
             "  refine ⟨hs, ?_, ?_, ?_, ?_⟩\n"
             "  · have : 0 < s.size := by omega\n    rw [getElem?_pos s 0 this]; simp [← getElem!_pos s 0 this, h0]\n"
             "  · rw [List.all_eq_true]\n    intro i hi\n    have hi' : i < ops.length := by simp at hi; omega\n"
             "    have hlt : i + 1 < s.size := by omega\n    simp only [decide_eq_true_eq]\n"
             "    rw [getElem?_pos s (i+1) hlt, ← getElem!_pos s (i+1) hlt, hstep i hi']\n"
             "  · intro hany\n    exact hany\n"
             "  · intro hnone\n    rw [← Array.all_toList, List.all_eq_true]\n    simp only [decide_eq_true_eq]\n"
             "    rw [Refine.forall_mem_toList_iff_idx]\n    intro k hk\n    rcases k with _ | k\n    · rw [h0]\n"
             "    · have hn := List.any_eq_false.mp hnone k (List.mem_range.mpr (by omega))\n"
             "      simp only [decide_eq_true_eq] at hn\n      omega"}

_IDXMONO = {
    "name": "idxOf_filter_mono",
    "statement": "∀ (p : Int → Bool) (l : List Int) (x y : Int), p x = true → p y = true → l.idxOf x ≤ l.idxOf y → "
                 "(l.filter p).idxOf x ≤ (l.filter p).idxOf y",
    "proof": "by intro p l\n  induction l with\n  | nil => intro x y _ _ _; simp\n  | cons a t ih =>\n    intro x y hx hy h\n"
             "    by_cases hax : a = x\n    · subst hax\n      by_cases hpa : p a = true\n      · simp [List.filter_cons, hpa]\n"
             "      · exact absurd hx hpa\n    · by_cases hay : a = y\n      · subst hay\n"
             "        have : (a :: t).idxOf a = 0 := List.idxOf_cons_self\n"
             "        have h2 : (a :: t).idxOf x = (t.idxOf x) + 1 := by simp [List.idxOf_cons, hax]\n        omega\n"
             "      · have h1 : (a :: t).idxOf x = t.idxOf x + 1 := by simp [List.idxOf_cons, hax]\n"
             "        have h2 : (a :: t).idxOf y = t.idxOf y + 1 := by simp [List.idxOf_cons, hay]\n"
             "        have := ih x y hx hy (by omega)\n        by_cases hpa : p a = true\n"
             "        · simp [List.filter_cons, hpa, List.idxOf_cons, hax, hay]; omega\n"
             "        · have hpa' : p a = false := by simpa using hpa\n          simp [List.filter_cons, hpa']; exact this"}
_FEN_EXIT = {
    "name": "fen_exit",
    "statement": "∀ (arr result : Array Int) (h : findEvenNumbers_precond arr), result.toList = arr.toList.filter isEven → "
                 "findEvenNumbers_postcond arr result h",
    "proof": "by intro arr result h hr\n  unfold findEvenNumbers_postcond\n  refine ⟨?_, ?_, ?_⟩\n"
             "  · rw [← Array.all_toList, List.all_eq_true]\n    intro x hx\n    rw [hr] at hx\n    have he := (List.mem_filter.mp hx)\n"
             "    simp only [decide_eq_true_eq]\n    refine ⟨by simpa using he.2, he.1, ?_⟩\n"
             "    rw [hr, List.count_filter]; simp [he.2]\n"
             "  · rw [← Array.all_toList, List.all_eq_true]\n    intro x hx\n    simp only [decide_eq_true_eq]\n    intro hev\n"
             "    rw [hr]; exact List.mem_filter.mpr ⟨hx, hev⟩\n"
             "  · rw [← Array.all_toList, List.all_eq_true]\n    intro x hx\n    rw [← Array.all_toList, List.all_eq_true]\n"
             "    intro y hy\n    simp only [decide_eq_true_eq]\n    intro hx' hy' hle\n    rw [hr]\n"
             "    exact idxOf_filter_mono isEven arr.toList x y hx' hy' hle"}
_EXIT34 = {
    "name": "exit34",
    "statement": "∀ (arr acc : Array Int) (i : Nat) (h : findEvenNumbers_precond arr), "
                 "(i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven) → ¬ i < arr.size → findEvenNumbers_postcond arr acc h",
    "proof": "by intro arr acc i h hinv hn\n  obtain ⟨hi, hacc⟩ := hinv\n  have hi' : i = arr.size := by omega\n  subst hi'\n"
             "  have ht : arr.toList.take arr.size = arr.toList := List.take_of_length_le (by simp)\n  rw [ht] at hacc\n"
             "  exact fen_exit arr acc h hacc"}

ORACLES_MORE = {
    "verina_basic_35": with_lemmas(term("Array.mk (arr.toList.filter (· ≠ 0) ++ arr.toList.filter (· = 0))"), [_MZ]),
    "verina_basic_39": with_lemmas(
        cases("l.length = 0", term("l"),
              term("(List.range l.length).map (fun i : Nat => l.getD (Int.toNat ((Int.ofNat i - Int.ofNat n + Int.ofNat l.length) % "
                   "Int.ofNat l.length)) (l.headD 0))")), [_ROT]),
    "verina_basic_56": with_lemmas(
        loop([["i", "Nat"], ["r", "Array Int"]], ["0", "dest"], _INV56, "i < len", "len - i", "r",
             term("(i + 1, r.set! (dStart + i) src[sStart + i]!)")), [_SETGET, _STEP56, _EXIT56]),
    "verina_basic_108": with_lemmas(
        bind("s", "Array Int", "s.size = operations.length + 1 ∧ s[0]! = 0 ∧ ∀ i, i < operations.length → s[i+1]! = s[i]! + operations[i]!",
             loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[0]"],
                  "i ≤ operations.length ∧ acc.size = i + 1 ∧ acc[0]! = 0 ∧ ∀ j, j < i → acc[j+1]! = acc[j]! + operations[j]!",
                  "i < operations.length", "operations.length - i", "acc",
                  term("(i + 1, acc.push (acc[i]! + operations[i]!))")),
             term("(s, (List.range operations.length).any (fun i => decide (s[i+1]! < 0)))")), [_EXIT108]),
    "verina_basic_34": with_lemmas(
        loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"], "i ≤ arr.size ∧ acc.toList = (arr.toList.take i).filter isEven",
             "i < arr.size", "arr.size - i", "acc",
             term("(i + 1, if isEven arr[i]! then acc.push arr[i]! else acc)")), [_IDXMONO, _FEN_EXIT, _EXIT34]),
}
