r"""Hand-written derivations for Verina tasks, batch N (advanced: first-fit searches with a witness lemma, counting, partitions)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import lemma

# --- 52 minOperations: the smallest prefix of the reversed list that holds 1..k -----------------------------------------------
_COV52 = "(((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r)) = true)"
_COV52_R = "(((List.range k).map (· + 1)).all (fun n => List.elem n ((nums.reverse).take r')) = true)"
_EXIT52 = {
    "name": "exit52",
    "statement": f"∀ (nums : List Nat) (k : Nat) (h : minOperations_precond nums k) (r : Nat), "
                 f"(r ≤ nums.length ∧ ∀ r', r' < r → ¬ {_COV52_R}) → ¬ (r < nums.length ∧ ¬ {_COV52}) → minOperations_postcond nums k r h",
    "proof": "by intro nums k h r hinv hg\n  obtain ⟨hr, hmin⟩ := hinv\n"
             f"  have hcov : {_COV52} := by\n    by_cases hlt : r < nums.length\n    · by_contra hn; exact hg ⟨hlt, hn⟩\n"
             "    · have hrl : r = nums.length := by omega\n      subst hrl\n      rw [List.all_eq_true]; intro n hn\n"
             "      have hm : n ∈ nums := by have := List.all_eq_true.mp h n hn; simpa using this\n"
             "      rw [List.take_of_length_le (by simp)]; simpa using hm\n"
             "  unfold minOperations_postcond\n  dsimp only\n  refine ⟨hcov, ?_⟩\n"
             "  by_cases hpos : r > 0\n  · rw [if_pos hpos]; exact hmin (r - 1) (by omega)\n"
             "  · rw [if_neg hpos]\n    have hr0 : r = 0 := by omega\n    subst hr0\n    by_contra hk0\n    have hk : k ≠ 0 := by simpa using hk0\n"
             "    have h1 := List.all_eq_true.mp hcov 1 (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)\n    simp at h1"}

_STEP52 = {
    "name": "step52",
    "statement": f"∀ (nums : List Nat) (k : Nat) (r : Nat), (r ≤ nums.length ∧ ∀ r', r' < r → ¬ {_COV52_R}) → "
                 f"(r < nums.length ∧ ¬ {_COV52}) → (r + 1 ≤ nums.length ∧ ∀ r', r' < r + 1 → ¬ {_COV52_R})",
    "proof": "by intro nums k r hinv hg\n  obtain ⟨hr, hmin⟩ := hinv\n  obtain ⟨hlt, hn⟩ := hg\n  refine ⟨by omega, fun r' hr' => ?_⟩\n"
             "  by_cases he : r' = r\n  · subst he; exact hn\n  · exact hmin r' (by omega)"}

# --- 55 mostFrequent --------------------------------------------------------------------------------------------------------
_CNT55 = "fun x => xs.countP (fun y => y = x)"
_E55 = f"(xs.find? (fun x => decide (xs.countP (fun y => y = x) = (xs.map ({_CNT55})).foldl max 0))).getD 0"
_A55 = {
    "name": "most55_a",
    "statement": "∀ (xs : List Int) (h : mostFrequent_precond xs) (r : Int), r ∈ xs → "
                 "(∀ x, x ∈ xs → xs.countP (fun y => y = x) ≤ xs.countP (fun y => y = r)) → "
                 "xs.find? (fun x => decide (xs.countP (fun y => y = x) = xs.countP (fun y => y = r))) = some r → "
                 "mostFrequent_postcond xs r h",
    "proof": "by intro xs h r hmem hall hfirst\n  unfold mostFrequent_postcond\n  dsimp only\n"
             "  refine ⟨hmem, List.all_eq_true.mpr fun x hx => by simpa using hall x hx, ?_⟩\n"
             "  rw [List.head?_filter]; exact hfirst"}
_L55 = {
    "name": "most55",
    "statement": f"∀ (xs : List Int) (h : mostFrequent_precond xs), mostFrequent_postcond xs ({_E55}) h",
    "proof": "by intro xs h\n"
             f"  have hne : xs.map ({_CNT55}) ≠ [] := by simpa using h\n"
             "  obtain ⟨h1, h2⟩ := Refine.maxlist_nat _ hne\n  rw [List.contains_iff_mem, List.mem_map] at h1\n"
             "  obtain ⟨x0, hx0, hcx0⟩ := h1\n"
             f"  have hany : xs.any (fun x => decide ((xs.countP (fun y => y = x)) = (xs.map ({_CNT55})).foldl max 0)) = true :=\n"
             "    List.any_eq_true.mpr ⟨x0, hx0, by simpa using hcx0⟩\n"
             "  obtain ⟨r, hr, hmem, hp⟩ := Refine.find_some_of_any xs _ hany\n"
             "  have hcr := of_decide_eq_true hp\n"
             f"  have e : {_E55} = r := by rw [hr]; rfl\n"
             "  rw [e]\n"
             "  refine most55_a xs h r hmem ?_ ?_\n"
             "  · intro x hx\n    have := List.all_eq_true.mp h2 _ (List.mem_map.mpr ⟨x, hx, rfl⟩)\n"
             "    rw [hcr]; simpa using this\n"
             "  · rw [hcr]; exact hr"}

# --- 56 moveZeroes --------------------------------------------------------------------------------------------------------------
_E56 = "xs.filter (fun x => decide (x ≠ 0)) ++ xs.filter (fun x => decide (x = 0))"
_ISSUB = {
    "name": "isSub_append",
    "statement": "∀ (F Z : List Int), isSubsequence F (F ++ Z) = true",
    "proof": "by intro F Z\n  induction F with\n  | nil => simp [isSubsequence]\n  | cons a t ih => simp [isSubsequence, ih]"}
_CNTV = {
    "name": "countVal_eq",
    "statement": "∀ (v : Int) (l : List Int), countVal v l = l.count v",
    "proof": "by intro v l\n  induction l with\n  | nil => simp [countVal]\n"
             "  | cons a t ih => simp only [countVal, ih, List.count_cons]; split_ifs <;> simp_all"}
_L56 = {
    "name": "move56",
    "statement": f"∀ (xs : List Int) (h : moveZeroes_precond xs), moveZeroes_postcond xs ({_E56}) h",
    "proof": "by intro xs h\n  unfold moveZeroes_postcond\n"
             "  have hperm : (xs.filter (fun x => decide (x ≠ 0)) ++ xs.filter (fun x => decide (x = 0))).Perm xs := by\n"
             "    have := List.filter_append_perm (fun x : Int => decide (x ≠ 0)) xs\n    simpa using this\n"
             "  refine ⟨isSub_append _ _, ?_, ?_, ?_⟩\n"
             "  · rw [List.all_eq_true]; intro x hx\n    rw [List.dropWhile_append] at hx\n    split_ifs at hx with hemp\n"
             "    · have := List.dropWhile_subset _ hx\n      simpa using (List.mem_filter.mp this).2\n"
             "    · exfalso; apply hemp\n"
             "      have : List.dropWhile (fun x => decide (x ≠ 0)) (xs.filter (fun x => decide (x ≠ 0))) = [] :=\n"
             "        List.dropWhile_eq_nil_iff.mpr (fun y hy => (List.mem_filter.mp hy).2)\n      simp [this]\n"
             "  · rw [countVal_eq, countVal_eq]; exact (hperm.count_eq 0).symm\n"
             "  · exact hperm.length_eq.symm"}

# --- 54 missingNumber -------------------------------------------------------------------------------------------------------------
_E54 = "((List.range (nums.length + 1)).find? (fun x => decide (x ∉ nums))).getD 0"
_L54 = {
    "name": "missing54",
    "statement": f"∀ (nums : List Nat) (h : missingNumber_precond nums), missingNumber_postcond nums ({_E54}) h",
    "proof": "by intro nums h\n  obtain ⟨hall, hnd⟩ := h\n"
             "  have hsub : nums ⊆ List.range (nums.length + 1) := fun x hx => List.mem_range.mpr (by\n"
             "    have := List.all_eq_true.mp hall x hx; simp at this; omega)\n"
             "  have hex : ∃ x ∈ List.range (nums.length + 1), x ∉ nums := by\n"
             "    by_contra hno\n    push_neg at hno\n    have hsub2 : List.range (nums.length + 1) ⊆ nums := fun x hx => hno x hx\n"
             "    have := (List.nodup_range.subperm hsub2).length_le\n    simp at this\n"
             "  have hany : (List.range (nums.length + 1)).any (fun x => decide (x ∉ nums)) = true :=\n"
             "    List.any_eq_true.mpr (by obtain ⟨x, hx, hn⟩ := hex; exact ⟨x, hx, by simpa using hn⟩)\n"
             "  obtain ⟨r, hr, hmem, hp⟩ := Refine.find_some_of_any _ _ hany\n"
             "  have hrn : r ∉ nums := by simpa using hp\n"
             "  unfold missingNumber_postcond\n  dsimp only\n  rw [hr, Option.getD_some]\n"
             "  refine ⟨hmem, hrn, ?_⟩\n  intro x hx hxr\n  by_contra hxn\n"
             "  have hsub3 : nums ⊆ ((List.range (nums.length + 1)).erase x).erase r := by\n"
             "    intro y hy\n    have hyr : y ≠ r := fun e => hrn (e ▸ hy)\n    have hyx : y ≠ x := fun e => hxn (e ▸ hy)\n"
             "    rw [List.mem_erase_of_ne hyr, List.mem_erase_of_ne hyx]; exact hsub hy\n"
             "  have hl := (hnd.subperm hsub3).length_le\n"
             "  have hrmem : r ∈ (List.range (nums.length + 1)).erase x := (List.mem_erase_of_ne (Ne.symm hxr)).mpr hmem\n"
             "  rw [List.length_erase_of_mem hrmem, List.length_erase_of_mem hx] at hl\n  simp at hl\n"
             "  have hxlt := List.mem_range.mp hx\n  have hrlt := List.mem_range.mp hmem\n  omega"}

# --- 8 canCompleteCircuit ----------------------------------------------------------------------------------------------------------
def _v8(k):
    return ("(List.range gas.length).all (fun i => decide ((List.range (i + 1)).foldl (fun t j => "
            f"t + gas[({k} + j) % gas.length]! - cost[({k} + j) % gas.length]!) 0 ≥ 0))")


_EXIT8 = {
    "name": "exit8",
    "statement": "∀ (gas cost : List Int) (h : canCompleteCircuit_precond gas cost) (s : Nat), "
                 f"(s ≤ gas.length ∧ ∀ k, k < s → ¬ ({_v8('k')} = true)) → ¬ (s < gas.length ∧ ¬ ({_v8('s')} = true)) → "
                 "canCompleteCircuit_postcond gas cost (if s < gas.length then (s : Int) else -1) h",
    "proof": "by intro gas cost h s hinv hg\n  obtain ⟨hs, hk⟩ := hinv\n  unfold canCompleteCircuit_postcond\n  intro valid\n"
             f"  have hv : ∀ k, valid k = ({_v8('k')}) := fun k => rfl\n"
             "  by_cases hlt : s < gas.length\n"
             "  · have hvs : valid s = true := by\n      rw [hv]; by_contra hn; exact hg ⟨hlt, hn⟩\n"
             "    rw [if_pos hlt]\n    refine ⟨by omega, fun hneg => by omega, fun _ => ⟨by simpa using hlt, by simpa using hvs, ?_⟩⟩\n"
             "    rw [List.all_eq_true]; intro k hk'\n    have hk2 := hk k (by simpa using List.mem_range.mp hk')\n"
             "    simp only [Int.toNat_natCast] at hk'\n    have := hk k (List.mem_range.mp hk')\n"
             "    simpa [hv] using this\n"
             "  · have hsl : s = gas.length := by omega\n    subst hsl\n    rw [if_neg hlt]\n"
             "    refine ⟨by omega, fun _ => ?_, fun hge => by omega⟩\n"
             "    rw [List.all_eq_true]; intro k hk'\n    have := hk k (List.mem_range.mp hk')\n    simpa [hv] using this"}

_STEP8 = {
    "name": "step8",
    "statement": "∀ (gas cost : List Int) (s : Nat), "
                 f"(s ≤ gas.length ∧ ∀ k, k < s → ¬ ({_v8('k')} = true)) → (s < gas.length ∧ ¬ ({_v8('s')} = true)) → "
                 f"(s + 1 ≤ gas.length ∧ ∀ k, k < s + 1 → ¬ ({_v8('k')} = true))",
    "proof": "by intro gas cost s hinv hg\n  obtain ⟨hs, hk⟩ := hinv\n  obtain ⟨hlt, hn⟩ := hg\n  refine ⟨by omega, fun k hk' => ?_⟩\n"
             "  by_cases he : k = s\n  · subst he; exact hn\n  · exact hk k (by omega)"}

ORACLES_MORE = {
    "verina_advanced_52": with_lemmas(
        loop([["r", "Nat"]], ["0"], f"r ≤ nums.length ∧ ∀ r', r' < r → ¬ {_COV52_R}", f"r < nums.length ∧ ¬ {_COV52}",
             "nums.length - r", "r", term("r + 1")), [_EXIT52, _STEP52]),
    "verina_advanced_55": with_lemmas(term(f"({_E55})"), [_A55, _L55]),
    "verina_advanced_56": with_lemmas(term(f"({_E56})"), [_ISSUB, _CNTV, _L56]),
    "verina_advanced_54": with_lemmas(term(_E54), [_L54]),
    "verina_advanced_8": with_lemmas(
        loop([["s", "Nat"]], ["0"], f"s ≤ gas.length ∧ ∀ k, k < s → ¬ ({_v8('k')} = true)",
             f"s < gas.length ∧ ¬ ({_v8('s')} = true)", "gas.length - s", "if s < gas.length then (s : Int) else -1", term("s + 1")),
        [_EXIT8, _STEP8]),
}
