r"""Hand-written derivations for Verina tasks, batch M (advanced: brute-force decisions over triples/pairs, first-fit searches)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas
from benchmarks.datasets.verina_oracle_i import lemma

_TRIPLE = ("let nums' := nums.zipIdx; nums'.any (fun (x, i) => nums'.any (fun (y, j) => nums'.any (fun (z, k) => "
           "decide (i < j ∧ j < k ∧ x < y ∧ y < z))))")

_SUBS24 = "lengthOfLIS_postcond.subsequences"
_INC24 = "lengthOfLIS_postcond.isStrictlyIncreasing"
_E24 = f"let allIncreasing := {_SUBS24} nums |>.filter (fun l => {_INC24} l); (((allIncreasing.map List.length).foldl max 0 : Nat) : Int)"
_SUBNIL24 = {
    "name": "sub_nil24",
    "statement": f"∀ (xs : List Int), [] ∈ {_SUBS24} xs",
    "proof": f"by intro xs\n  induction xs with\n  | nil => simp [{_SUBS24}]\n"
             f"  | cons a t ih => simp only [{_SUBS24}]; exact List.mem_append.mpr (Or.inl ih)"}

_HI = "hasChordIntersection_postcond.hasIntersection"
_SORTED13 = ("let sortedChords := chords.map (fun chord => let a := chord[0]!; let b := chord[1]!; "
             "if a > b then [b, a] else [a, b]); ")
_E13 = _SORTED13 + f"sortedChords.any (fun x => sortedChords.any (fun y => {_HI} x y))"
_SYM13 = {
    "name": "has_symm13",
    "statement": f"∀ (x y : List Nat), {_HI} x y = {_HI} y x",
    "proof": f"by intro x y\n  unfold {_HI}\n  exact Bool.or_comm _ _"}
_IRR13 = {
    "name": "has_irr13",
    "statement": f"∀ (x : List Nat), {_HI} x x = false",
    "proof": f"by intro x\n  unfold {_HI}\n  simp"}

_NOT_SORTED53 = "¬ List.Pairwise (· ≤ ·) (nums.rotateRight j)"
_EXIT53 = {
    "name": "exit53",
    "statement": "∀ (nums : List Int) (h : minimumRightShifts_precond nums) (j : Nat), ¬ nums.length ≤ 1 → "
                 "(j ≤ nums.length ∧ ∀ k, k < j → ¬ List.Pairwise (· ≤ ·) (nums.rotateRight k)) → "
                 "¬ (j < nums.length ∧ ¬ List.Pairwise (· ≤ ·) (nums.rotateRight j)) → "
                 "minimumRightShifts_postcond nums (if j < nums.length then (j : Int) else -1) h",
    "proof": "by intro nums h j hn hinv hg\n  obtain ⟨hj, hk⟩ := hinv\n  unfold minimumRightShifts_postcond\n  dsimp only\n"
             "  rw [if_neg (by omega)]\n"
             "  by_cases hlt : j < nums.length\n"
             "  · left\n    have hs : List.Pairwise (· ≤ ·) (nums.rotateRight j) := by\n      by_contra hns\n      exact hg ⟨hlt, hns⟩\n"
             "    rw [if_pos hlt]\n    refine ⟨by omega, by omega, by simpa using hs, ?_⟩\n"
             "    rw [List.all_eq_true]; intro k hk'\n    have := hk k (by simpa using hk')\n    simpa using this\n"
             "  · right\n    have : j = nums.length := by omega\n    subst this\n    rw [if_neg hlt]\n    refine ⟨rfl, ?_⟩\n"
             "    rw [List.all_eq_true]; intro k hk'\n    have := hk k (by simpa using hk')\n    simpa using this"}
_NIL53 = {
    "name": "nil53",
    "statement": "∀ (nums : List Int) (h : minimumRightShifts_precond nums), nums.length ≤ 1 → minimumRightShifts_postcond nums 0 h",
    "proof": "by intro nums h hn\n  unfold minimumRightShifts_postcond\n  dsimp only\n  rw [if_pos hn]"}

ORACLES_MORE = {
    "verina_advanced_15": with_lemmas(
        term(f"({_TRIPLE})"),
        [lemma("trip15", "increasingTriplet", "(nums : List Int)", ["nums"], _TRIPLE,
               "intro nums'\n  refine ⟨fun hr => hr, fun hn => ?_⟩\n"
               "  have hn' : (nums'.any (fun (x, i) => nums'.any (fun (y, j) => nums'.any (fun (z, k) => "
               "decide (i < j ∧ j < k ∧ x < y ∧ y < z))))) ≠ true := hn\n"
               "  simp only [ne_eq, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hn' ⊢\n"
               "  rintro ⟨x, i⟩ hx ⟨y, j⟩ hy ⟨z, k⟩ hz\n  by_contra hc\n  apply hn'\n"
               "  exact ⟨(x, i), hx, (y, j), hy, (z, k), hz, by omega⟩")]),
    "verina_advanced_24": with_lemmas(
        term(f"({_E24})"),
        [_SUBNIL24, lemma("lis24", "lengthOfLIS", "(nums : List Int)", ["nums"], _E24,
                          "intro allIncreasing\n  have hnil : [] ∈ allIncreasing := List.mem_filter.mpr ⟨sub_nil24 nums, by "
                          f"simp [{_INC24}]⟩\n  have hs := Refine.maxlen_spec allIncreasing hnil\n"
                          "  exact ⟨by simpa using hs.1, by simpa using hs.2⟩")]),
    "verina_advanced_13": with_lemmas(
        term(f"({_E13})"),
        [_SYM13, _IRR13, lemma("chord13", "hasChordIntersection", "(N : Nat) (chords : List (List Nat))", ["N", "chords"], _E13,
                               "intro sortedChords\n  refine ⟨fun hpw hres => ?_, fun hany => hany⟩\n"
                               f"  have hres' : (sortedChords.any (fun x => sortedChords.any (fun y => {_HI} x y))) = true := hres\n"
                               "  obtain ⟨x, hx, hy'⟩ := List.any_eq_true.mp hres'\n  obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp hy'\n"
                               "  by_cases hxe : x = y\n  · subst hxe; rw [has_irr13] at hxy; exact absurd hxy (by simp)\n"
                               f"  · haveI : Std.Symm (fun a b : List Nat => (!{_HI} a b) = true) := "
                               f"⟨fun a b h => by simpa [has_symm13 a b] using h⟩\n"
                               "    have hpw' := List.Pairwise.forall hpw hx hy hxe\n"
                               "    simp [hxy] at hpw'")]),
    "verina_advanced_53": cases(
        "nums.length ≤ 1",
        with_lemmas(term("0"), [_NIL53]),
        with_lemmas(
            loop([["j", "Nat"]], ["0"], "j ≤ nums.length ∧ ∀ k, k < j → ¬ List.Pairwise (· ≤ ·) (nums.rotateRight k)",
                 "j < nums.length ∧ ¬ List.Pairwise (· ≤ ·) (nums.rotateRight j)", "nums.length - j",
                 "if j < nums.length then (j : Int) else -1", term("j + 1")), [_EXIT53])),
}
