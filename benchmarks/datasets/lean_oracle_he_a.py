r"""Hand-written derivations for HumanEval 000-132 that had none (batch file A: problems 0-19).

Each entry is a derivation tree (see ``derivation_dsl.py``); the engine proves its obligations and certifies the finished term.
Kinds: *loop* (an invariant), *restate* (one ``term``/``cases`` for a decidable specification), *definitional*.
"""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_UNIQUE_SORTED = {
    "name": "unique_sorted_ok",
    "statement": "∀ (l : List Int), (∀ i, i < ((l.dedup).mergeSort (fun a b => decide (a ≤ b))).length - 1 → ((l.dedup).mergeSort (fun a b => decide (a ≤ b)))[i]! < ((l.dedup).mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ (∀ x ∈ (l.dedup).mergeSort (fun a b => decide (a ≤ b)), x ∈ l) ∧ ∀ x ∈ l, x ∈ (l.dedup).mergeSort (fun a b => decide (a ≤ b))",
    "proof": "by\n  intro l\n  have hp : ((l.dedup).mergeSort (fun a b => decide (a ≤ b))).Perm l.dedup := List.mergeSort_perm _ _\n  have hnd : ((l.dedup).mergeSort (fun a b => decide (a ≤ b))).Nodup := hp.nodup_iff.mpr ((List.nodup_dedup _))\n  have hsort : List.Pairwise (fun a b => decide (a ≤ b) = true) ((l.dedup).mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) _\n  refine ⟨?_, ?_, ?_⟩\n  · intro i hi\n    have hi' : i + 1 < ((l.dedup).mergeSort (fun a b => decide (a ≤ b))).length := by omega\n    rw [List.Nodup, List.pairwise_iff_getElem] at hnd\n    rw [List.pairwise_iff_getElem] at hsort\n    have h1 := hnd i (i + 1) (by omega) hi' (by omega)\n    have h2 := hsort i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    simp at h2\n    omega\n  · intro x hx\n    simpa using hx\n  · intro x hx\n    simpa using hx"
}
_COMMON_SORTED = {
    "name": "common_sorted_ok",
    "statement": "∀ (l1 l2 : List Int), (∀ i, i < (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))).length - 1 → (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)))[i]! < (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)))[i + 1]!) ∧ (∀ x ∈ ((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b)), x ∈ l1 ∧ x ∈ l2) ∧ ∀ x ∈ l1, x ∈ l2 → x ∈ ((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))",
    "proof": "by\n  intro l1 l2\n  have hp : (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))).Perm (l1.filter (fun x => decide (x ∈ l2))).dedup :=\n    List.mergeSort_perm _ _\n  have hnd : (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))).Nodup :=\n    hp.nodup_iff.mpr ((List.nodup_dedup _))\n  have hsort : List.Pairwise (fun a b => decide (a ≤ b) = true)\n      (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) _\n  refine ⟨?_, ?_, ?_⟩\n  · intro i hi\n    have hi' : i + 1 < (((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))).length := by omega\n    rw [List.Nodup, List.pairwise_iff_getElem] at hnd\n    rw [List.pairwise_iff_getElem] at hsort\n    have h1 := hnd i (i + 1) (by omega) hi' (by omega)\n    have h2 := hsort i (i + 1) (by omega) hi' (by omega)\n    rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n    simp at h2\n    omega\n  · intro x hx\n    simpa using hx\n  · intro x hx h2\n    simpa using ⟨hx, h2⟩"
}

_SORT_NAT = {
    "name": "sortNat_ok",
    "statement": "∀ (L : List Nat), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!",
    "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≤ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (L.mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≤ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
}
_SORT_INT = {
    "name": "sortInt_ok",
    "statement": "∀ (L : List Int), (L.mergeSort (fun a b => decide (a ≤ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≤ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≤ b)))[i]! ≤ (L.mergeSort (fun a b => decide (a ≤ b)))[i + 1]!",
    "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≤ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≤ b) = true) (L.mergeSort (fun a b => decide (a ≤ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≤ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
}
_SORT_INT_DESC = {
    "name": "sortIntDesc_ok",
    "statement": "∀ (L : List Int), (L.mergeSort (fun a b => decide (a ≥ b))).isPerm L = true ∧ ∀ i, i < (L.mergeSort (fun a b => decide (a ≥ b))).length - 1 → (L.mergeSort (fun a b => decide (a ≥ b)))[i]! ≥ (L.mergeSort (fun a b => decide (a ≥ b)))[i + 1]!",
    "proof": "by\n  intro L\n  have hp : (L.mergeSort (fun a b => decide (a ≥ b))).Perm L := List.mergeSort_perm L _\n  refine ⟨List.isPerm_iff.mpr hp, ?_⟩\n  intro i hi\n  have hs : List.Pairwise (fun a b => decide (a ≥ b) = true) (L.mergeSort (fun a b => decide (a ≥ b))) :=\n    List.pairwise_mergeSort (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) L\n  rw [List.pairwise_iff_getElem] at hs\n  have hi' : i + 1 < (L.mergeSort (fun a b => decide (a ≥ b))).length := by omega\n  have := hs i (i + 1) (by omega) hi' (by omega)\n  rw [getElem!_pos _ i (by omega), getElem!_pos _ (i + 1) hi']\n  simpa using this"
}

_PALIN = [
    {
        "name": "len_filter_range_succ",
        "statement": "∀ (p : Nat → Bool) (i : Nat), ((List.range (i + 1)).filter p).length = ((List.range i).filter p).length + (if p i = true then 1 else 0)",
        "proof": "by\n  intro p i\n  rw [List.range_succ, List.filter_append, List.length_append]\n  by_cases h : p i = true <;> simp [h]"
    },
    {
        "name": "palin_step",
        "statement": "∀ (n i e o : Nat), i < n + 1 → (i ≤ n + 1 ∧ e = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ o = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length) → (i + 1 ≤ n + 1 ∧ (if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0 then e + 1 else e) = ((List.range (i + 1)).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ (if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1 then o + 1 else o) = ((List.range (i + 1)).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length)",
        "proof": "by\n  intro n i e o hi ⟨_, he, ho⟩\n  refine ⟨by omega, ?_, ?_⟩\n  · rw [len_filter_range_succ, ← he]\n    simp only [decide_eq_true_eq]\n    split <;> omega\n  · rw [len_filter_range_succ, ← ho]\n    simp only [decide_eq_true_eq]\n    split <;> omega"
    }
]

ORACLES_MORE = {
    # he_000: two nested scans, the inner one decides "some earlier element is close to numbers[j]"
    "he_000_has_close_elements": loop(
        [["j", "Nat"], ["found", "Bool"]], ["0", "false"],
        "j ≤ numbers.length ∧ (found = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ |numbers[a]! - numbers[b]!| < threshold)",
        "j < numbers.length", "numbers.length - j", "found",
        bind("hit", "Bool", "hit = true ↔ ∃ a, a < j ∧ |numbers[a]! - numbers[j]!| < threshold",
             loop([["i", "Nat"], ["seen", "Bool"]], ["0", "false"],
                  "i ≤ j ∧ (seen = true ↔ ∃ a, a < i ∧ |numbers[a]! - numbers[j]!| < threshold)", "i < j", "j - i", "seen",
                  term("(i + 1, seen || decide (|numbers[i]! - numbers[j]!| < threshold))")),
             term("(j + 1, found || hit)"))),
    "he_002_truncate_number": term("number - (⌊number⌋ : ℚ)"),
    # he_004: the mean by a loop, then the deviations by a loop
    "he_004_mean_absolute_deviation": bind(
        "m", "ℚ", "m = numbers.sum / (numbers.length : ℚ)",
        loop([["i", "Nat"], ["s", "ℚ"]], ["0", "0"], "i ≤ numbers.length ∧ s = (numbers.take i).sum", "i < numbers.length",
             "numbers.length - i", "s / (numbers.length : ℚ)", term("(i + 1, s + numbers[i]!)")),
        loop([["i", "Nat"], ["d", "ℚ"]], ["0", "0"],
             "i ≤ numbers.length ∧ d = ((numbers.take i).map (fun x => |x - m|)).sum", "i < numbers.length",
             "numbers.length - i", "d / (numbers.length : ℚ)", term("(i + 1, d + |numbers[i]! - m|)"))),
    "he_007_filter_by_substring": loop(
        [["i", "Nat"], ["acc", "List String"]], ["0", "[]"],
        "i ≤ strings.length ∧ acc = (strings.take i).filter (fun s => decide (hasSub s substring))", "i < strings.length",
        "strings.length - i", "acc",
        term("(i + 1, if decide (hasSub strings[i]! substring) then acc ++ [strings[i]!] else acc)")),
    "he_008_sum_product": loop(
        [["i", "Nat"], ["s", "Int"], ["p", "Int"]], ["0", "0", "1"],
        "i ≤ numbers.length ∧ s = (numbers.take i).sum ∧ p = (numbers.take i).prod", "i < numbers.length",
        "numbers.length - i", "(s, p)", term("(i + 1, s + numbers[i]!, p * numbers[i]!)")),
    "he_011_string_xor": loop(
        [["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
        "i ≤ a.length ∧ acc = (List.range i).map (fun k => if a.toList[k]! = b.toList[k]! then '0' else '1')",
        "i < a.length", "a.length - i", "String.mk acc",
        term("(i + 1, acc ++ [if a.toList[i]! = b.toList[i]! then '0' else '1'])")),
    "he_012_longest": cases(
        "strings = []", term("none"),
        with_lemmas(
            bind("b", "Nat", "b < strings.length ∧ (∀ j, j < strings.length → strings[j]!.length ≤ strings[b]!.length) ∧ "
                             "∀ j, j < b → strings[j]!.length < strings[b]!.length",
                 loop([["k", "Nat"], ["b", "Nat"]], ["1", "0"],
                      "1 ≤ k ∧ k ≤ strings.length ∧ b < k ∧ (∀ j, j < k → strings[j]!.length ≤ strings[b]!.length) ∧ "
                      "∀ j, j < b → strings[j]!.length < strings[b]!.length",
                      "k < strings.length", "strings.length - k", "b",
                      term("(k + 1, if strings[k]!.length > strings[b]!.length then k else b)")),
                 term("some strings[b]!")),
            [{"name": "longest_exit",
              "statement": "∀ (strings : List String) (b : Nat), (b < strings.length ∧ (∀ j, j < strings.length → strings[j]!.length ≤ strings[b]!.length) ∧ "
                           "∀ j, j < b → strings[j]!.length < strings[b]!.length) → "
                           "∃ i, i < strings.length ∧ strings[i]! = strings[b]! ∧ (∀ t ∈ strings, t.length ≤ strings[b]!.length) ∧ "
                           "∀ j, j < i → strings[j]!.length < strings[b]!.length",
              "proof": "by intro strings b h\n  obtain ⟨hb, h1, h2⟩ := h\n  refine ⟨b, hb, rfl, ?_, h2⟩\n"
                       "  intro t ht\n  obtain ⟨k, hk, rfl⟩ := (Refine.mem_iff_idx strings t).mp ht\n  exact h1 k hk"}])),
    "he_014_all_prefixes": loop(
        [["i", "Nat"], ["acc", "List String"]], ["0", "[]"],
        "i ≤ string.length ∧ acc.length = i ∧ ∀ k, k < i → acc[k]! = String.mk (string.toList.take (k + 1))",
        "i < string.length", "string.length - i", "acc",
        term("(i + 1, acc ++ [String.mk (string.toList.take (i + 1))])")),
    "he_016_count_distinct": term("(s.toLower.toList.eraseDups).length"),
    "he_018_how_many_times": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ string.length ∧ acc = ((List.range i).filter (fun j => substring.toList.isPrefixOf (string.toList.drop j))).length",
        "i < string.length", "string.length - i", "acc",
        term("(i + 1, if substring.toList.isPrefixOf (string.toList.drop i) then acc + 1 else acc)")),

    # --- problems 20-40 ---
    "he_006_parse_nested_parens": bind(
        "groups", "List String", 'groups = (paren_string.splitOn " ").filter (fun g => g != "")',
        term('(paren_string.splitOn " ").filter (fun g => g != "")'),
        loop([["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
             "i ≤ groups.length ∧ acc = (groups.take i).map (fun g => maxDepth g.toList)", "i < groups.length",
             "groups.length - i", "acc", term("(i + 1, acc ++ [maxDepth groups[i]!.toList])"))),
    "he_013_gcd": with_lemmas(
        term("Nat.gcd a b"),
        [{"name": "gcd_ok",
          "statement": "∀ (a b : Nat), a > 0 → b > 0 → (Nat.gcd a b > 0 ∧ a % Nat.gcd a b = 0 ∧ b % Nat.gcd a b = 0 ∧ "
                       "∀ d, d < a + b + 1 → d > 0 → a % d = 0 → b % d = 0 → d ≤ Nat.gcd a b)",
          "proof": "by intro a b ha hb\n  have hp : Nat.gcd a b > 0 := Nat.gcd_pos_of_pos_left b ha\n"
                   "  refine ⟨hp, Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b), Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b), ?_⟩\n"
                   "  intro d _ hd h1 h2\n  exact Nat.le_of_dvd hp (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2))"}]),
    "he_017_parse_music": bind(
        "notes", "List String", 'notes = (if music_string = "" then [] else music_string.splitOn " ")',
        term('if music_string = "" then [] else music_string.splitOn " "'),
        loop([["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
             'i ≤ notes.length ∧ acc = (notes.take i).map (fun n => if n = "o" then 4 else if n = "o|" then 2 else 1)',
             "i < notes.length", "notes.length - i", "acc",
             term('(i + 1, acc ++ [if notes[i]! = "o" then 4 else if notes[i]! = "o|" then 2 else 1])'))),
    "he_021_rescale_to_unit": bind(
        "lo", "ℚ", "lo = numbers.foldl min numbers[0]!",
        loop([["i", "Nat"], ["m", "ℚ"]], ["0", "numbers[0]!"],
             "i ≤ numbers.length ∧ m = (numbers.take i).foldl min numbers[0]!", "i < numbers.length", "numbers.length - i", "m",
             term("(i + 1, min m numbers[i]!)")),
        bind("hi", "ℚ", "hi = numbers.foldl max numbers[0]!",
             loop([["i", "Nat"], ["m", "ℚ"]], ["0", "numbers[0]!"],
                  "i ≤ numbers.length ∧ m = (numbers.take i).foldl max numbers[0]!", "i < numbers.length", "numbers.length - i",
                  "m", term("(i + 1, max m numbers[i]!)")),
             loop([["i", "Nat"], ["acc", "List ℚ"]], ["0", "[]"],
                  "i ≤ numbers.length ∧ acc = (numbers.take i).map (fun x => (x - lo) / (hi - lo))", "i < numbers.length",
                  "numbers.length - i", "acc", term("(i + 1, acc ++ [(numbers[i]! - lo) / (hi - lo)])")))),
    "he_022_filter_integers": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
             "i ≤ values.length ∧ acc = (values.take i).filterMap (fun v => match v with | PyVal.int n => some n | _ => none)",
             "i < values.length", "values.length - i", "acc",
             term("(i + 1, match values[i]? with | some (PyVal.int n) => acc ++ [n] | _ => acc)")),
        [{"name": "pyval_take_succ", "statement": "∀ (l : List PyVal) (i : Nat), l.take (i + 1) = l.take i ++ l[i]?.toList",
          "proof": "by intro l i\n  exact List.take_succ"}]),
    "he_026_remove_duplicates": loop(
        [["i", "Nat"], ["acc", "List Int"]], ["0", "[]"],
        "i ≤ numbers.length ∧ acc = (numbers.take i).filter (fun x => numbers.count x = 1)", "i < numbers.length",
        "numbers.length - i", "acc",
        term("(i + 1, if numbers.count numbers[i]! = 1 then acc ++ [numbers[i]!] else acc)")),
    "he_027_flip_case": loop(
        [["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
        "i ≤ string.length ∧ acc = (List.range i).map (fun k => flipChar string.toList[k]!)", "i < string.length",
        "string.length - i", "String.mk acc", term("(i + 1, acc ++ [flipChar string.toList[i]!])")),
    "he_036_fizz_buzz": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ n ∧ acc = (((List.range i).filter (fun j => j % 11 = 0 ∨ j % 13 = 0)).map (fun j => (toString j).toList.count '7')).sum",
        "i < n", "n - i", "acc",
        term("(i + 1, if i % 11 = 0 ∨ i % 13 = 0 then acc + (toString i).toList.count '7' else acc)")),
    "he_040_triples_sum_to_zero": loop(
        [["k", "Nat"], ["found", "Bool"]], ["0", "false"],
        "k ≤ l.length ∧ (found = true ↔ ∃ c, c < k ∧ ∃ b, b < c ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[c]! = 0)",
        "k < l.length", "l.length - k", "found",
        bind("hitk", "Bool", "hitk = true ↔ ∃ b, b < k ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[k]! = 0",
             loop([["j", "Nat"], ["fj", "Bool"]], ["0", "false"],
                  "j ≤ k ∧ (fj = true ↔ ∃ b, b < j ∧ ∃ a, a < b ∧ l[a]! + l[b]! + l[k]! = 0)", "j < k", "k - j", "fj",
                  bind("hitj", "Bool", "hitj = true ↔ ∃ a, a < j ∧ l[a]! + l[j]! + l[k]! = 0",
                       loop([["i", "Nat"], ["fi", "Bool"]], ["0", "false"],
                            "i ≤ j ∧ (fi = true ↔ ∃ a, a < i ∧ l[a]! + l[j]! + l[k]! = 0)", "i < j", "j - i", "fi",
                            term("(i + 1, fi || decide (l[i]! + l[j]! + l[k]! = 0))")),
                       term("(j + 1, fj || hitj)"))),
             term("(k + 1, found || hitk)"))),

    # --- problems 44-70 ---
    "he_034_unique": with_lemmas(term("(l.dedup).mergeSort (fun a b => decide (a ≤ b))"), [_UNIQUE_SORTED]),
    "he_058_common": with_lemmas(
        term("((l1.filter (fun x => decide (x ∈ l2))).dedup).mergeSort (fun a b => decide (a ≤ b))"), [_COMMON_SORTED]),
    "he_045_triangle_area": term("a * h / 2"),
    "he_046_fib4": with_lemmas(
        loop([["i", "Nat"], ["a", "Nat"], ["b", "Nat"], ["c", "Nat"], ["d", "Nat"]], ["0", "0", "0", "2", "0"],
             "i ≤ n ∧ a = fib4Spec i ∧ b = fib4Spec (i + 1) ∧ c = fib4Spec (i + 2) ∧ d = fib4Spec (i + 3)", "i < n", "n - i", "a",
             term("(i + 1, b, c, d, a + b + c + d)")),
        [{"name": "fib4_step", "statement": "∀ (i : Nat), fib4Spec (i + 4) = fib4Spec (i + 3) + fib4Spec (i + 2) + fib4Spec (i + 1) + fib4Spec i",
          "proof": "by intro i\n  rw [fib4Spec]"},
         {"name": "fib4_base", "statement": "fib4Spec 0 = 0 ∧ fib4Spec 1 = 0 ∧ fib4Spec 2 = 2 ∧ fib4Spec 3 = 0",
          "proof": "by refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl"}]),
    "he_063_fibfib": with_lemmas(
        loop([["i", "Nat"], ["a", "Nat"], ["b", "Nat"], ["c", "Nat"]], ["0", "0", "0", "1"],
             "i ≤ n ∧ a = fibfibSpec i ∧ b = fibfibSpec (i + 1) ∧ c = fibfibSpec (i + 2)", "i < n", "n - i", "a",
             term("(i + 1, b, c, a + b + c)")),
        [{"name": "fibfib_step", "statement": "∀ (i : Nat), fibfibSpec (i + 3) = fibfibSpec (i + 2) + fibfibSpec (i + 1) + fibfibSpec i",
          "proof": "by intro i\n  rw [fibfibSpec]"},
         {"name": "fibfib_base", "statement": "fibfibSpec 0 = 0 ∧ fibfibSpec 1 = 0 ∧ fibfibSpec 2 = 1",
          "proof": "by refine ⟨?_, ?_, ?_⟩ <;> rfl"}]),
    "he_049_modp": with_lemmas(
        loop([["i", "Nat"], ["acc", "Nat"]], ["0", "1 % p"], "i ≤ n ∧ acc = 2 ^ i % p", "i < n", "n - i", "acc",
             term("(i + 1, acc * 2 % p)")),
        [{"name": "pow_mod_step", "statement": "∀ (i p : Nat), 2 ^ (i + 1) % p = 2 ^ i % p * 2 % p",
          "proof": "by intro i p\n  rw [Nat.pow_succ, Nat.mod_mul_mod]"}]),
    "he_051_remove_vowels": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
             "i ≤ text.length ∧ acc = (text.toList.take i).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))",
             "i < text.length", "text.length - i", "String.mk acc",
             term("(i + 1, if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains text.toList[i]! then acc else acc ++ [text.toList[i]!])")),
        [{"name": "vowel_step",
          "statement": "∀ (text : String) (i : Nat) (acc : List Char), i < text.length → acc = (text.toList.take i).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)) → "
                       "(if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains text.toList[i]! then acc else acc ++ [text.toList[i]!]) = (text.toList.take (i + 1)).filter (fun c => !(['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c))",
          "proof": "by intro text i acc hi h\n  subst h\n  have hi' : i < text.toList.length := hi\n"
                   "  rw [Refine.filter_take_succ_bang _ text.toList i hi']\n"
                   "  cases hv : ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains text.toList[i]! <;> simp"}]),
    "he_053_add": term("x + y"),
    "he_054_same_chars": bind(
        "a", "Bool", "a = true ↔ ∀ c ∈ s0.toList, c ∈ s1.toList",
        loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
             "i ≤ s0.length ∧ (ok = true ↔ ∀ k, k < i → s0.toList[k]! ∈ s1.toList)", "i < s0.length", "s0.length - i", "ok",
             term("(i + 1, ok && decide (s0.toList[i]! ∈ s1.toList))")),
        bind("b", "Bool", "b = true ↔ ∀ c ∈ s1.toList, c ∈ s0.toList",
             loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                  "i ≤ s1.length ∧ (ok = true ↔ ∀ k, k < i → s1.toList[k]! ∈ s0.toList)", "i < s1.length", "s1.length - i", "ok",
                  term("(i + 1, ok && decide (s1.toList[i]! ∈ s0.toList))")),
             term("a && b"))),
    "he_056_correct_bracketing": loop(
        [["i", "Nat"], ["d", "Int"], ["ok", "Bool"]], ["0", "0", "true"],
        "i ≤ brackets.length ∧ d = ((brackets.toList.take i).count '<' : Int) - ((brackets.toList.take i).count '>' : Int) ∧ "
        "(ok = true ↔ ∀ k, k ≤ i → (brackets.toList.take k).count '>' ≤ (brackets.toList.take k).count '<')",
        "i < brackets.length", "brackets.length - i", "ok && decide (d = 0)",
        term("(i + 1, d + (if brackets.toList[i]! = '<' then 1 else if brackets.toList[i]! = '>' then -1 else 0), "
             "ok && decide (d + (if brackets.toList[i]! = '<' then 1 else if brackets.toList[i]! = '>' then -1 else 0) ≥ 0))")),
    "he_064_vowels_count": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ s.length ∧ acc = ((s.toList.take i).filter (fun c => ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains c)).length",
        "i < s.length", "s.length - i", "acc + (if s.toList.getLast? = some 'y' ∨ s.toList.getLast? = some 'Y' then 1 else 0)",
        term("(i + 1, if ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'].contains s.toList[i]! then acc + 1 else acc)")),
    "he_065_circular_shift": bind(
        "d", "List Char", "d = (toString x).toList", term("(toString x).toList"),
        term("String.mk (if shift > d.length then d.reverse else d.drop (d.length - shift % d.length) ++ d.take (d.length - shift % d.length))")),
    "he_067_fruit_distribution": term('n - ((s.splitOn " ")[0]!).toNat! - ((s.splitOn " ")[3]!).toNat!'),
    "he_070_strange_sort_list": bind(
        "s", "List Int", "s = lst.mergeSort (fun a b => a ≤ b)", term("lst.mergeSort (fun a b => a ≤ b)"),
        term("(List.range lst.length).map (fun k => if k % 2 = 0 then s[k / 2]! else s[lst.length - 1 - k / 2]!)")),

    # --- problems 71-96 ---
    "he_073_smallest_change": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ arr.length / 2 ∧ acc = ((List.range i).filter (fun k => arr[k]! ≠ arr[arr.length - 1 - k]!)).length",
        "i < arr.length / 2", "arr.length / 2 - i", "acc",
        term("(i + 1, if arr[i]! ≠ arr[arr.length - 1 - i]! then acc + 1 else acc)")),
    "he_074_total_match": cases("(lst1.map String.length).sum ≤ (lst2.map String.length).sum", term("lst1"), term("lst2")),
    "he_075_is_multiply_prime": term(
        "decide (∃ p, p < a + 1 ∧ ∃ q, q < a + 1 ∧ ∃ r, r < a + 1 ∧ p * q * r = a ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r)"),
    "he_076_is_simple_power": loop(
        [["i", "Nat"], ["f", "Bool"]], ["0", "false"],
        "i ≤ x.natAbs + 3 ∧ (f = true ↔ ∃ k, k < i ∧ 1 ≤ k ∧ n ^ k = x)", "i < x.natAbs + 3", "x.natAbs + 3 - i",
        "decide (x = 1) || f", term("(i + 1, f || decide (1 ≤ i ∧ n ^ i = x))")),
    "he_077_iscube": loop(
        [["i", "Nat"], ["f", "Bool"]], ["0", "false"],
        "i ≤ a.natAbs + 2 ∧ (f = true ↔ ∃ k, k < i ∧ k ^ 3 = a.natAbs)", "i < a.natAbs + 2", "a.natAbs + 2 - i", "f",
        term("(i + 1, f || decide (i ^ 3 = a.natAbs))")),
    "he_078_hex_key": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ num.length ∧ acc = ((num.toList.take i).filter (fun c => ['2', '3', '5', '7', 'B', 'D'].contains c)).length",
        "i < num.length", "num.length - i", "acc",
        term("(i + 1, if ['2', '3', '5', '7', 'B', 'D'].contains num.toList[i]! then acc + 1 else acc)")),
    "he_080_is_happy": loop(
        [["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
        "i ≤ s.length - 2 ∧ (ok = true ↔ ∀ k, k < i → s.toList[k]! ≠ s.toList[k + 1]! ∧ s.toList[k]! ≠ s.toList[k + 2]! ∧ "
        "s.toList[k + 1]! ≠ s.toList[k + 2]!)",
        "i < s.length - 2", "s.length - 2 - i", "decide (s.length ≥ 3) && ok",
        term("(i + 1, ok && decide (s.toList[i]! ≠ s.toList[i + 1]! ∧ s.toList[i]! ≠ s.toList[i + 2]! ∧ s.toList[i + 1]! ≠ s.toList[i + 2]!))")),
    "he_081_numerical_letter_grade": loop(
        [["i", "Nat"], ["acc", "List String"]], ["0", "[]"],
        "i ≤ grades.length ∧ acc = (List.range i).map (fun k => letterGrade grades[k]!)", "i < grades.length",
        "grades.length - i", "acc", term("(i + 1, acc ++ [letterGrade grades[i]!])")),
    "he_082_prime_length": term("decide (Nat.Prime string.length)"),
    "he_083_starts_one_ends": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ 10 ^ n ∧ acc = ((List.range i).filter (fun m => 10 ^ (n - 1) ≤ m ∧ (m / 10 ^ (n - 1) = 1 ∨ m % 10 = 1))).length",
        "i < 10 ^ n", "10 ^ n - i", "acc",
        term("(i + 1, if 10 ^ (n - 1) ≤ i ∧ (i / 10 ^ (n - 1) = 1 ∨ i % 10 = 1) then acc + 1 else acc)")),
    "he_089_encrypt": loop(
        [["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
        "i ≤ s.length ∧ acc = (List.range i).map (fun k => rot4 s.toList[k]!)", "i < s.length", "s.length - i", "String.mk acc",
        term("(i + 1, acc ++ [rot4 s.toList[i]!])")),
    "he_093_encode": loop(
        [["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
        "i ≤ message.length ∧ acc = (List.range i).map (fun k => encChar message.toList[k]!)", "i < message.length",
        "message.length - i", "String.mk acc", term("(i + 1, acc ++ [encChar message.toList[i]!])")),
    "he_091_is_bored": term('((((S.replace "?" ".").replace "!" ".").splitOn ".").map String.trim).filter (fun t => t.startsWith "I ") |>.length'),
    "he_095_check_dict_case": term("decide (keys ≠ []) && (keys.all lowerKey || keys.all upperKey)"),
    "he_096_count_up_to": with_lemmas(
        loop([["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
             "i ≤ n ∧ acc = (List.range i).filter (fun p => decide (Nat.Prime p))", "i < n", "n - i", "acc",
             term("(i + 1, if Nat.Prime i then acc ++ [i] else acc)")),
        [{"name": "count_up_to_exit",
          "statement": "∀ (n : Nat) (acc : List Nat), (n ≤ n ∧ acc = (List.range n).filter (fun p => decide (Nat.Prime p))) → "
                       "(∀ p ∈ acc, p < n ∧ Nat.Prime p) ∧ (∀ p, p < n → Nat.Prime p → p ∈ acc) ∧ "
                       "∀ i, i < acc.length - 1 → acc[i]! < acc[i + 1]!",
          "proof": "by intro n acc h\n  obtain ⟨_, rfl⟩ := h\n  refine ⟨?_, ?_, Refine.sorted_filter_range n _⟩\n"
                   "  · intro p hp\n    simpa using hp\n  · intro p hp hpr\n    simpa using ⟨hp, hpr⟩"}]),

    # --- problems 47 and 101-132 ---
    "he_047_median": bind(
        "s", "List ℚ", "s = l.mergeSort (fun a b => a ≤ b)", term("l.mergeSort (fun a b => a ≤ b)"),
        term("if s.length % 2 = 1 then s[s.length / 2]! else (s[s.length / 2 - 1]! + s[s.length / 2]!) / 2")),
    "he_101_words_string": term('((s.map (fun c => if c == \',\' then \' \' else c)).splitOn " ").filter (fun w => w != "")'),
    "he_104_unique_digits": with_lemmas(
        term("(x.filter noEvenDigit).mergeSort (fun a b => decide (a ≤ b))"), [_SORT_NAT]),
    "he_105_by_length": bind(
        "ds", "List Int", "ds = arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)", term("arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)"),
        term("(ds.mergeSort (fun a b => a ≥ b)).map numName")),
    "he_106_f": loop(
        [["i", "Nat"], ["acc", "List Nat"]], ["0", "[]"],
        "i ≤ n ∧ acc = (List.range i).map (fun k => if (k + 1) % 2 = 0 then (k + 1).factorial else (k + 1) * (k + 2) / 2)",
        "i < n", "n - i", "acc",
        term("(i + 1, acc ++ [if (i + 1) % 2 = 0 then (i + 1).factorial else (i + 1) * (i + 2) / 2])")),
    "he_107_even_odd_palindrome": with_lemmas(
        loop([["i", "Nat"], ["e", "Nat"], ["o", "Nat"]], ["0", "0", "0"],
             "i ≤ n + 1 ∧ e = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 0))).length ∧ "
             "o = ((List.range i).filter (fun j => decide (1 ≤ j ∧ isPal (toString j).toList ∧ j % 2 = 1))).length",
             "i < n + 1", "n + 1 - i", "(e, o)",
             term("(i + 1, if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 0 then e + 1 else e, "
                  "if 1 ≤ i ∧ isPal (toString i).toList ∧ i % 2 = 1 then o + 1 else o)")),
        _PALIN),
    "he_108_count_nums": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ arr.length ∧ acc = ((arr.take i).filter (fun x => signedDigitSum x > 0)).length", "i < arr.length",
        "arr.length - i", "acc", term("(i + 1, if signedDigitSum arr[i]! > 0 then acc + 1 else acc)")),
    "he_109_move_one_ball": loop(
        [["i", "Nat"], ["f", "Bool"]], ["0", "false"],
        "i ≤ arr.length + 1 ∧ (f = true ↔ ∃ k, k < i ∧ arr.drop k ++ arr.take k = arr.mergeSort (fun a b => a ≤ b))",
        "i < arr.length + 1", "arr.length + 1 - i", "f",
        term("(i + 1, f || decide (arr.drop i ++ arr.take i = arr.mergeSort (fun a b => a ≤ b)))")),
    "he_110_exchange": cases(
        "(lst1.filter (fun x => x % 2 = 1)).length ≤ (lst2.filter (fun x => x % 2 = 0)).length",
        term('"YES"'), term('"NO"')),
    "he_112_reverse_delete": bind(
        "t", "List Char", "t = s.toList.filter (fun ch => !(c.toList.contains ch))",
        term("s.toList.filter (fun ch => !(c.toList.contains ch))"), term("(String.mk t, decide (t = t.reverse))")),
    "he_113_odd_count": loop(
        [["i", "Nat"], ["acc", "List String"]], ["0", "[]"],
        "i ≤ lst.length ∧ acc = (List.range i).map (fun k => oddMsg (oddDigits lst[k]!))", "i < lst.length",
        "lst.length - i", "acc", term("(i + 1, acc ++ [oddMsg (oddDigits lst[i]!)])")),
    "he_115_max_fill": loop(
        [["i", "Nat"], ["acc", "Nat"]], ["0", "0"],
        "i ≤ grid.length ∧ acc = ((grid.take i).map (fun row => (row.sum + capacity - 1) / capacity)).sum", "i < grid.length",
        "grid.length - i", "acc", term("(i + 1, acc + (grid[i]!.sum + capacity - 1) / capacity)")),
    "he_117_select_words": term(
        '(s.splitOn " ").filter (fun w => w != "" && (w.toList.filter (fun ch => !([\'a\', \'e\', \'i\', \'o\', \'u\', \'A\', \'E\', \'I\', \'O\', \'U\'].contains ch))).length == n)'),
    "he_119_match_parens": cases(
        "isBalanced (lst[0]!.toList ++ lst[1]!.toList) ∨ isBalanced (lst[1]!.toList ++ lst[0]!.toList)",
        term('"Yes"'), term('"No"')),
    "he_120_maximum": with_lemmas(
        term("((arr.mergeSort (fun a b => a ≥ b)).take k).mergeSort (fun a b => decide (a ≤ b))"), [_SORT_INT]),
    "he_122_add_elements": term("((arr.take k).filter (fun x => x.natAbs < 100)).sum"),
    "he_123_get_odd_collatz": with_lemmas(
        term("((collatzSeq 5000 n).filter (fun x => x % 2 = 1)).mergeSort (fun a b => decide (a ≤ b))"), [_SORT_NAT]),
    "he_127_intersection": cases(
        "min interval1.2 interval2.2 - max interval1.1 interval2.1 ≥ 2 ∧ Nat.Prime (min interval1.2 interval2.2 - max interval1.1 interval2.1).toNat",
        term('"YES"'), term('"NO"')),
    "he_128_prod_signs": term(
        "if arr = [] then none else some ((arr.map (fun (x : Int) => (x.natAbs : Int))).sum * (arr.map Int.sign).prod)"),
    "he_131_digits": term(
        "if ((toString n).toList.map (fun c => c.toNat - 48)).any (fun d => d % 2 = 1) then "
        "(((toString n).toList.map (fun c => c.toNat - 48)).filter (fun d => d % 2 = 1)).prod else 0"),

    # --- more restatements and small searches ---
    "he_124_valid_date": bind(
        "l", "List Char", "l = date.toList", term("date.toList"),
        term("decide (l.length = 10 ∧ l[2]! = '-' ∧ l[5]! = '-' ∧ (l.take 2).all Char.isDigit = true ∧ "
             "((l.drop 3).take 2).all Char.isDigit = true ∧ (l.drop 6).all Char.isDigit = true ∧ 1 ≤ natOf (l.take 2) ∧ "
             "natOf (l.take 2) ≤ 12 ∧ 1 ≤ natOf ((l.drop 3).take 2) ∧ natOf ((l.drop 3).take 2) ≤ daysIn (natOf (l.take 2)))")),
    "he_125_split_words": bind(
        "hasWhite", "Bool", "hasWhite = txt.toList.any (fun c => c == ' ' || c == '\\n' || c == '\\r' || c == '\\t')",
        term("txt.toList.any (fun c => c == ' ' || c == '\\n' || c == '\\r' || c == '\\t')"),
        term("if hasWhite = true then Sum.inl (splitWhite txt) else if txt.toList.contains ',' then Sum.inl (txt.splitOn \",\") "
             "else Sum.inr ((txt.toList.filter (fun c => c.isLower && (c.toNat - 97) % 2 = 1)).length)")),
    "he_102_choose_num": cases(
        "y < x", term("-1"),
        cases("y % 2 = 0", term("y"), cases("x ≤ y - 1", term("y - 1"), term("-1")))),
}
