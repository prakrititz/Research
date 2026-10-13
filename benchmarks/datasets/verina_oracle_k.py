r"""Hand-written derivations for Verina tasks, batch K (advanced: decidable characterisations and majority elements)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import lemma

_POW4 = {
    "name": "pow4_iff",
    "statement": "∀ (n : Nat), (∃ m : Nat, n = 4 ^ m) ↔ (List.range (n + 1)).any (fun m => decide (n = 4 ^ m)) = true",
    "proof": "by intro n\n  constructor\n  · rintro ⟨m, hm⟩\n    rw [List.any_eq_true]\n"
             "    have hlt : m < 4 ^ m := Nat.lt_pow_self (by omega)\n"
             "    refine ⟨m, List.mem_range.mpr (by omega), by simpa using hm⟩\n"
             "  · intro h\n    obtain ⟨m, _, hm⟩ := List.any_eq_true.mp h\n    exact ⟨m, by simpa using hm⟩"}

_POW2 = {
    "name": "pow2_iff",
    "statement": "∀ (n : Int), (∃ x : Nat, _root_.pow 2 x = n ∧ n > 0) ↔ "
                 "(List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0)) = true",
    "proof": "by intro n\n"
             "  have hp : ∀ x : Nat, _root_.pow 2 x = (2 : Int) ^ x := by\n    intro x\n    induction x with\n"
             "    | zero => simp [_root_.pow]\n    | succ k ih => simp [_root_.pow, ih, pow_succ]; ring\n"
             "  constructor\n  · rintro ⟨x, hx, hn⟩\n    rw [List.any_eq_true]\n"
             "    refine ⟨x, List.mem_range.mpr ?_, by simpa using ⟨hx, hn⟩⟩\n"
             "    have h1 : x < 2 ^ x := Nat.lt_pow_self (by omega)\n    rw [hp] at hx\n"
             "    have h2 : ((2 ^ x : Nat) : Int) = n := by rw [← hx]; push_cast; ring\n    omega\n"
             "  · intro h\n    obtain ⟨x, _, hx⟩ := List.any_eq_true.mp h\n    exact ⟨x, by simpa using hx⟩"}

_DIGIT8 = {
    "name": "digit8_iff",
    "statement": "∀ (absN : Nat), (∃ i : Nat, absN / (10 ^ i) % 10 = 8) ↔ "
                 "(List.range (absN + 1)).any (fun i => decide (absN / (10 ^ i) % 10 = 8)) = true",
    "proof": "by intro absN\n  constructor\n  · rintro ⟨i, hi⟩\n    rw [List.any_eq_true]\n"
             "    refine ⟨i, List.mem_range.mpr ?_, by simpa using hi⟩\n    by_contra hge\n"
             "    have h1 : i < 10 ^ i := Nat.lt_pow_self (by omega)\n"
             "    have h2 : absN / 10 ^ i = 0 := Nat.div_eq_of_lt (by omega)\n    rw [h2] at hi; simp at hi\n"
             "  · intro h\n    obtain ⟨i, _, hx⟩ := List.any_eq_true.mp h\n    exact ⟨i, by simpa using hx⟩"}

_PEAK = ("let len := lst.length; let validPeaks := List.range len |>.filter (fun p => 1 ≤ p ∧ p < len - 1 ∧ "
         "(List.range p).all (fun i => lst[i]! < lst[i + 1]!) ∧ "
         "(List.range (len - 1 - p)).all (fun i => lst[p + i]! > lst[p + i + 1]!)); ")

_MAJ = "xs.find? (fun x => decide (xs.count x > xs.length / 2))"
_SEQ74 = ("let n := nums.length; let getSubarray_local := fun (i j : Nat) => (nums.drop i).take (j - i + 1); "
          "let distinctCount_local := fun (l : List Nat) => let foldFn := fun (seen : List Nat) (x : Nat) => "
          "if seen.elem x then seen else x :: seen; let distinctElems := l.foldl foldFn []; distinctElems.length; "
          "let square_local := fun (n : Nat) => n * n; "
          "List.range n |>.foldl (fun (outerSum : Nat) (i : Nat) => let innerSum : Nat := "
          "List.range (n - i) |>.foldl (fun (currentInnerSum : Nat) (d : Nat) => let j := i + d; "
          "let subarr := getSubarray_local i j; let count := distinctCount_local subarr; "
          "currentInnerSum + square_local count) 0; outerSum + innerSum) 0")

_SQ48 = {
    "name": "sq48",
    "statement": "∀ (n r : Nat), (r * r ≤ n ∧ n < (r + 1) * (r + 1)) → (decide (r * r = n) = true ↔ ∃ i : Nat, i * i = n)",
    "proof": "by intro n r hr\n  obtain ⟨h1, h2⟩ := hr\n  simp only [decide_eq_true_eq]\n  constructor\n"
             "  · intro h; exact ⟨r, h⟩\n"
             "  · rintro ⟨i, hi⟩\n    rcases lt_trichotomy i r with hlt | heq | hgt\n"
             "    · exfalso; nlinarith\n    · subst heq; exact hi\n    · exfalso; nlinarith"}

ORACLES_MORE = {
    "verina_advanced_14": with_lemmas(
        term("(List.range (n + 1)).any (fun m => decide (n = 4 ^ m))"),
        [_POW4, lemma("pow4_ok", "ifPowerOfFour", "(n : Nat)", ["n"], "(List.range (n + 1)).any (fun m => decide (n = 4 ^ m))",
                      "exact (pow4_iff n).symm")]),
    "verina_advanced_23": with_lemmas(
        term("(List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0))"),
        [_POW2, lemma("pow2_ok", "isPowerOfTwo", "(n : Int)", ["n"], "(List.range (n.toNat + 1)).any (fun x => decide (_root_.pow 2 x = n ∧ n > 0))",
                      "split_ifs with hb\n  · exact (pow2_iff n).mpr hb\n  · intro hex; exact hb ((pow2_iff n).mp hex)")]),
    "verina_advanced_20": with_lemmas(
        term("(n % 8 == 0) || (List.range (n.natAbs + 1)).any (fun i => n.natAbs / (10 ^ i) % 10 == 8)"),
        [_DIGIT8, lemma("eight_ok", "isItEight", "(n : Int)", ["n"],
                        "(n % 8 == 0) || (List.range (n.natAbs + 1)).any (fun i => n.natAbs / (10 ^ i) % 10 == 8)",
                        "intro absN\n  have hd := digit8_iff absN\n  simp only [beq_iff_eq, Bool.or_eq_true] at hd ⊢\n  "
                        "simp only [beq_eq_decide] at hd ⊢\n  rw [← hd]")]),
    "verina_advanced_22": with_lemmas(
        term(f"({_PEAK}validPeaks != [])"),
        [lemma("peak_ok", "isPeakValley", "(lst : List Int)", ["lst"], f"{_PEAK}validPeaks != []",
               "intro len validPeaks\n  refine ⟨fun hb => hb, fun hl hb => ?_⟩\n"
               "  have hb' : (validPeaks != []) = true := hb\n  have h0 := List.length_eq_zero_iff.mp hl\n  rw [h0] at hb'\n  simp at hb'")]),
    "verina_advanced_36": with_lemmas(
        term(f"({_MAJ}).getD 0"),
        [lemma("maj36", "majorityElement", "(xs : List Nat)", ["xs"], f"({_MAJ}).getD 0",
               "obtain ⟨r, hr, hc, _⟩ := Refine.find_majority xs h.2\n  "
               "have hr' : ({_MAJ}).getD 0 = r := hr\n  show xs.count (({_MAJ}).getD 0) > xs.length / 2\n  rw [hr']; exact hc".replace("{_MAJ}", _MAJ))]),
}
ORACLES_MORE.update({
    "verina_advanced_35": with_lemmas(
        term("(nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0"),
        [lemma("maj35", "majorityElement", "(nums : List Int)", ["nums"],
               "(nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0",
               "obtain ⟨r, hr, hc, hu⟩ := Refine.find_majority nums h.2\n  "
               "rw [show (nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0 = r from hr]\n  exact ⟨hc, hu⟩")]),
    "verina_advanced_37": with_lemmas(
        term("(nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0"),
        [lemma("maj37", "majorityElement", "(nums : List Int)", ["nums"],
               "(nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0",
               "obtain ⟨r, hr, hc, hu⟩ := Refine.find_majority nums h.2\n  "
               "rw [show (nums.find? (fun x => decide (nums.count x > nums.length / 2))).getD 0 = r from hr]\n  "
               "refine ⟨hc, List.all_eq_true.mpr fun x hx => ?_⟩\n  by_cases hxr : x = r\n  · simp [hxr]\n"
               "  · have := hu x hx hxr; simp [this]")]),
    "verina_advanced_66": with_lemmas(
        term("String.intercalate \" \" (((words_str.splitOn \" \").filter (fun w => w ≠ \"\")).reverse)"),
        [lemma("rev66", "reverseWords", "(words_str : String)", ["words_str"],
               "String.intercalate \" \" (((words_str.splitOn \" \").filter (fun w => w ≠ \"\")).reverse)", "exact ⟨_, rfl, rfl⟩")]),
    "verina_basic_48": bind("r", "Nat", "r * r ≤ n ∧ n < (r + 1) * (r + 1)",
                            loop([["r", "Nat"]], ["0"], "r * r ≤ n", "(r + 1) * (r + 1) ≤ n", "n - r", "r", term("r + 1")),
                            with_lemmas(term("decide (r * r = n)"),
                                        [_SQ48, {"name": "sq48_ok", "statement": "∀ (n r : Nat), (r * r ≤ n ∧ n < (r + 1) * (r + 1)) → "
                                                 "isPerfectSquare_postcond n (decide (r * r = n))",
                                                 "proof": "by intro n r hr\n  unfold isPerfectSquare_postcond\n  exact sq48 n r hr"}])),
    "verina_advanced_74": with_lemmas(
        term(f"({_SEQ74})"),
        [lemma("seq74", "solution", "(nums : List Nat)", ["nums"], _SEQ74, "intro n g d sq hpre\n  exact ⟨Nat.zero_le _, rfl⟩", no_precond=True)]),
})
