r"""Hand-written derivations for Verina tasks, batch Q (basic: symmetric difference, set-to-sequence)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_INARR = {'name': 'inArray_iff', 'statement': '∀ (a : Array Int) (x : Int), inArray a x = true ↔ x ∈ a.toList', 'proof': 'by\n  intro a x\n  unfold inArray\n  rw [← Array.any_toList, List.any_eq_true]\n  constructor\n  · rintro ⟨y, hy, hxy⟩\n    have : y = x := by simpa using hxy\n    subst this; exact hy\n  · intro h; exact ⟨x, h, by simp⟩\n'}
_E22 = '((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort (fun x y => decide (x ≤ y))).toArray'
_L22 = {'name': 'diss22', 'statement': '∀ (a b : Array Int) (h : dissimilarElements_precond a b), dissimilarElements_postcond a b (' + _E22 + ') h', 'proof': "by\n  intro a b h\n  have hmem : ∀ x, x ∈ ((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort\n      (fun x y => decide (x ≤ y))) ↔ (x ∈ a.toList ∧ x ∉ b.toList) ∨ (x ∈ b.toList ∧ x ∉ a.toList) := by\n    intro x\n    have hf : ∀ (c : Array Int) (y : Int), inArray c y = false ↔ y ∉ c.toList := by\n      intro c y; rw [← Bool.not_eq_true, inArray_iff]\n    rw [(List.mergeSort_perm _ _).mem_iff, List.mem_dedup, List.mem_append, List.mem_filter, List.mem_filter]\n    simp only [Bool.not_eq_true', hf]\n  have hnd : ((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort\n      (fun x y => decide (x ≤ y))).Nodup :=\n    (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_dedup _)\n  have hsort := List.pairwise_mergeSort' (· ≤ ·) ((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup)\n  unfold dissimilarElements_postcond\n  rw [List.toList_toArray]\n  refine ⟨?_, hsort, hnd, ?_, ?_⟩\n  · rw [← Array.all_toList, List.toList_toArray, List.all_eq_true]\n    intro x hx\n    have := (hmem x).mp hx\n    simp only [decide_eq_true_eq, ne_eq]\n    intro heq\n    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩\n    · have := (inArray_iff a x).mpr h1; rw [heq] at this; exact h2 ((inArray_iff b x).mp this)\n    · have := (inArray_iff b x).mpr h1; rw [← heq] at this; exact h2 ((inArray_iff a x).mp this)\n  · rw [← Array.all_toList, List.all_eq_true]\n    intro x hx\n    by_cases hb : x ∈ b.toList\n    · have hb' : x ∈ b := Array.mem_def.mpr hb\n      simp only [hb', if_true, decide_eq_true_eq]\n      intro hr\n      have hr' : x ∈ ((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort\n          (fun x y => decide (x ≤ y))) := by simpa using hr\n      rcases (hmem x).mp hr' with ⟨_, h2⟩ | ⟨h1, h2⟩\n      · exact h2 hb\n      · exact h2 hx\n    · have hb' : ¬ x ∈ b := fun h => hb (Array.mem_def.mp h)\n      simp only [hb', if_false, decide_eq_true_eq]\n      simpa using (hmem x).mpr (Or.inl ⟨hx, hb⟩)\n  · rw [← Array.all_toList, List.all_eq_true]\n    intro x hx\n    by_cases ha : x ∈ a.toList\n    · have ha' : x ∈ a := Array.mem_def.mpr ha\n      simp only [ha', if_true, decide_eq_true_eq]\n      intro hr\n      have hr' : x ∈ ((a.toList.filter (fun x => !inArray b x) ++ b.toList.filter (fun x => !inArray a x)).dedup.mergeSort\n          (fun x y => decide (x ≤ y))) := by simpa using hr\n      rcases (hmem x).mp hr' with ⟨h1, h2⟩ | ⟨_, h2⟩\n      · exact h2 hx\n      · exact h2 ha\n    · have ha' : ¬ x ∈ a := fun h => ha (Array.mem_def.mp h)\n      simp only [ha', if_false, decide_eq_true_eq]\n      simpa using (hmem x).mpr (Or.inr ⟨hx, ha⟩)\n"}

# --- 89 SetToSeq: first occurrences in order ---
_IDX1 = {"name": "idxOf_le_of_getElem", "statement": "∀ (s : List Int) (k : Nat) (a : Int), s[k]? = some a → s.idxOf a ≤ k",
         "proof": "by intro s k a h\n  induction s generalizing k with\n  | nil => simp at h\n  | cons x t ih =>\n    rcases k with _ | k\n    · simp at h; subst h; simp\n    · simp at h\n      by_cases hxa : x = a\n      · subst hxa; simp\n      · have := ih k h\n        simp [List.idxOf_cons, hxa]; omega"}
_IDX2 = {"name": "idxOf_take_lt", "statement": "∀ (s : List Int) (i : Nat) (a : Int), a ∈ s.take i → s.idxOf a < i",
         "proof": "by intro s i a h\n  obtain ⟨k, hk, hka⟩ := List.getElem_of_mem h\n  have hk' : k < i := by simp at hk; omega\n  have hks : k < s.length := by simp at hk; omega\n  have : s[k]? = some a := by\n    rw [List.getElem?_eq_getElem hks]; simp at hka; simp [hka]\n  have := idxOf_le_of_getElem s k a this\n  omega"}
_IDX3 = {"name": "idxOf_ge_of_not_mem_take", "statement": "∀ (s : List Int) (i : Nat) (x : Int), s[i]? = some x → x ∉ s.take i → i ≤ s.idxOf x",
         "proof": "by intro s i x hx h\n  have hmem : x ∈ s := List.mem_iff_getElem?.mpr ⟨i, hx⟩\n  by_contra hlt\n  have hlt' : s.idxOf x < i := by omega\n  have h1 : s.idxOf x < s.length := List.idxOf_lt_length_of_mem hmem\n  apply h\n  have := List.getElem_idxOf h1\n  rw [← this]\n  exact List.mem_iff_getElem.mpr ⟨s.idxOf x, by simp; omega, by simp⟩"}

_INV89 = "i ≤ s.length ∧ (∀ x, x ∈ acc ↔ x ∈ s.take i) ∧ acc.Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) acc"
_NEW89 = "(if acc.contains s[i]! then acc else acc ++ [s[i]!])"
_INV89N = "i + 1 ≤ s.length ∧ (∀ x, x ∈ " + _NEW89 + " ↔ x ∈ s.take (i + 1)) ∧ (" + _NEW89 + ").Nodup ∧ List.Pairwise (fun a b => s.idxOf a < s.idxOf b) " + _NEW89
_STEP89 = {
    "name": "step89",
    "statement": "∀ (s : List Int) (i : Nat) (acc : List Int), (" + _INV89 + ") → i < s.length → (" + _INV89N + ")",
    "proof": "by intro s i acc hinv hg\n  obtain ⟨_, hmem, hnd, hpw⟩ := hinv\n"
             "  have htake : s.take (i + 1) = s.take i ++ [s[i]!] := Refine.take_succ_bang s i hg\n"
             "  have hsi : s[i]? = some s[i]! := by rw [getElem!_pos s i hg]; exact List.getElem?_eq_getElem hg\n"
             "  by_cases hc : acc.contains s[i]! = true\n"
             "  · rw [if_pos hc]\n    have hin : s[i]! ∈ acc := List.contains_iff_mem.mp hc\n    have hin' := (hmem _).mp hin\n"
             "    refine ⟨by omega, fun x => ?_, hnd, hpw⟩\n    rw [hmem x, htake]\n    constructor\n"
             "    · intro h; exact List.mem_append.mpr (Or.inl h)\n"
             "    · intro h\n      rcases List.mem_append.mp h with h | h\n      · exact h\n      · rw [List.mem_singleton] at h; rw [h]; exact hin'\n"
             "  · rw [if_neg hc]\n    have hnin : s[i]! ∉ acc := fun h => hc (List.contains_iff_mem.mpr h)\n"
             "    refine ⟨by omega, fun x => ?_, ?_, ?_⟩\n"
             "    · rw [List.mem_append, hmem x, htake, List.mem_append]\n"
             "    · refine List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, ?_⟩\n      intro a ha b hb\n      rw [List.mem_singleton] at hb; subst hb\n"
             "      intro hab; exact hnin (hab ▸ ha)\n"
             "    · rw [List.pairwise_append]\n      refine ⟨hpw, List.pairwise_singleton _ _, ?_⟩\n"
             "      intro a ha b hb\n      rw [List.mem_singleton] at hb; subst hb\n"
             "      have h1 := idxOf_take_lt s i a ((hmem a).mp ha)\n"
             "      have hnt : s[i]! ∉ s.take i := fun h => hnin ((hmem _).mpr h)\n"
             "      have h2 := idxOf_ge_of_not_mem_take s i _ hsi hnt\n      omega"}
_EXIT89 = {
    "name": "exit89",
    "statement": "∀ (s : List Int) (h : SetToSeq_precond s) (i : Nat) (acc : List Int), (" + _INV89 + ") → ¬ i < s.length → SetToSeq_postcond s acc h",
    "proof": "by intro s h i acc hinv hn\n  obtain ⟨hi, hmem, hnd, hpw⟩ := hinv\n  have hi' : i = s.length := by omega\n  subst hi'\n"
             "  have ht : s.take s.length = s := List.take_of_length_le (le_refl _)\n  rw [ht] at hmem\n  unfold SetToSeq_postcond\n"
             "  refine ⟨?_, ?_, ?_, ?_⟩\n"
             "  · rw [List.all_eq_true]; intro a ha; simpa using (hmem a).mp ha\n"
             "  · rw [List.all_eq_true]; intro a ha; simpa using (hmem a).mpr ha\n"
             "  · rw [List.all_eq_true]; intro a ha; simpa using List.count_eq_one_of_mem hnd ha\n"
             "  · refine hpw.imp ?_\n    intro a b hab _\n    exact hab"}

ORACLES_MORE = {
    "verina_basic_22": with_lemmas(term("(" + _E22 + ")"), [_INARR, _L22]),
    "verina_basic_89": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"], _INV89, "i < s.length", "s.length - i", "acc",
             term("(i + 1, " + _NEW89 + ")")), [_IDX1, _IDX2, _IDX3, _STEP89, _EXIT89]),
}
