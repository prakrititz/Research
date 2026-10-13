r"""Hand-written derivations for Verina tasks, batch Z (basic: search in a matrix).

The specification only asks for *a* position holding the key (or the proof that there is none), so the derivation is the
plain row-by-row scan: an outer loop over rows whose body is an inner search of the row (a ``bind`` over a loop)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_INV = ("i ≤ a.size ∧ ((0 ≤ mm ∧ mm < a.size ∧ 0 ≤ nn ∧ nn < (a[0]!).size ∧ get2d a mm nn = key) ∨ "
        "(mm = -1 ∧ nn = -1 ∧ ∀ k, k < i → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key))")
_INV_N = ("i + 1 ≤ a.size ∧ ((0 ≤ (if jr = -1 then -1 else (i : Int)) ∧ (if jr = -1 then -1 else (i : Int)) < a.size ∧ 0 ≤ jr ∧ "
          "jr < (a[0]!).size ∧ get2d a (if jr = -1 then -1 else (i : Int)) jr = key) ∨ "
          "((if jr = -1 then -1 else (i : Int)) = -1 ∧ jr = -1 ∧ ∀ k, k < i + 1 → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key))")
_PROP = ("((jr = -1 ∧ ∀ j, j < (a[i]!).size → (a[i]!)[j]! ≠ key) ∨ "
         "(0 ≤ jr ∧ jr < (a[0]!).size ∧ (a[i]!)[jr.toNat]! = key))")
_PROP_J = ("((((if j < (a[i]!).size then (j : Int) else -1)) = -1 ∧ ∀ j', j' < (a[i]!).size → (a[i]!)[j']! ≠ key) ∨ "
           "(0 ≤ (if j < (a[i]!).size then (j : Int) else -1) ∧ (if j < (a[i]!).size then (j : Int) else -1) < (a[0]!).size ∧ "
           "(a[i]!)[(if j < (a[i]!).size then (j : Int) else -1).toNat]! = key))")

_WIDTH = {
    "name": "width90",
    "statement": "∀ (a : Array (Array Int)) (key : Int), SlopeSearch_precond a key → ∀ i, i < a.size → (a[i]!).size = (a[0]!).size",
    "proof": "by intro a key h i hi\n  obtain ⟨h0, _, hpw, _⟩ := h\n  rcases Nat.eq_zero_or_pos i with rfl | hpos\n  · rfl\n"
             "  · have := List.pairwise_iff_getElem.mp hpw 0 i (by simpa using h0) (by simpa using hi) hpos\n"
             "    rw [getElem!_pos a i hi, getElem!_pos a 0 h0]\n    simpa using this.symm"}
_INNER_EXIT = {
    "name": "inner90",
    "statement": "∀ (a : Array (Array Int)) (key : Int), SlopeSearch_precond a key → ∀ (i : Nat), i < a.size → ∀ (j : Nat), "
                 "(j ≤ (a[i]!).size ∧ ∀ j', j' < j → (a[i]!)[j']! ≠ key) → ¬ (j < (a[i]!).size ∧ (a[i]!)[j]! ≠ key) → " + _PROP_J,
    "proof": "by intro a key h i hi j hinv hn\n  obtain ⟨hj, hall⟩ := hinv\n  by_cases hlt : j < (a[i]!).size\n"
             "  · rw [if_pos hlt]\n    right\n    have hkey : (a[i]!)[j]! = key := by\n      by_contra hne\n      exact hn ⟨hlt, hne⟩\n"
             "    have hw := width90 a key h i hi\n    refine ⟨by omega, by simpa [hw] using hlt, ?_⟩\n    simpa using hkey\n"
             "  · rw [if_neg hlt]\n    left\n    have : j = (a[i]!).size := by omega\n    subst this\n    exact ⟨rfl, fun j' hj' => hall j' hj'⟩"}
_STEP = {
    "name": "step90",
    "statement": "∀ (a : Array (Array Int)) (key : Int) (i : Nat) (mm nn jr : Int), (" + _INV + ") → (i < a.size ∧ mm = -1) → " + _PROP +
                 " → (" + _INV_N.replace("jr = -1 ∧ ∀ k", "jr = -1 ∧ ∀ k") + ")",
    "proof": "by intro a key i mm nn jr hinv hg hprop\n  obtain ⟨hi, hd⟩ := hinv\n  obtain ⟨hlt, hmm⟩ := hg\n"
             "  have hall : ∀ k, k < i → ∀ j, j < (a[k]!).size → (a[k]!)[j]! ≠ key := by\n"
             "    rcases hd with ⟨h1, _⟩ | ⟨_, _, h3⟩\n    · omega\n    · exact h3\n"
             "  rcases hprop with ⟨hj, hrow⟩ | ⟨hj0, hj1, hkey⟩\n"
             "  · subst hj\n    refine ⟨by omega, Or.inr ⟨by simp, rfl, ?_⟩⟩\n    intro k hk j hjj\n"
             "    by_cases hki : k = i\n    · subst hki; exact hrow j hjj\n    · exact hall k (by omega) j hjj\n"
             "  · have hjne : jr ≠ -1 := by omega\n    rw [if_neg hjne]\n    refine ⟨by omega, Or.inl ⟨by omega, by omega, hj0, hj1, ?_⟩⟩\n"
             "    simp only [get2d, Int.toNat_natCast]\n    exact hkey"}
_EXIT = {
    "name": "exit90",
    "statement": "∀ (a : Array (Array Int)) (key : Int) (h : SlopeSearch_precond a key) (i : Nat) (mm nn : Int), (" + _INV +
                 ") → ¬ (i < a.size ∧ mm = -1) → SlopeSearch_postcond a key (mm, nn) h",
    "proof": "by intro a key h i mm nn hinv hn\n  obtain ⟨hi, hd⟩ := hinv\n  unfold SlopeSearch_postcond\n"
             "  rcases hd with ⟨h1, h2, h3, h4, h5⟩ | ⟨hm, hn', hall⟩\n  · exact Or.inl ⟨h1, h2, h3, h4, h5⟩\n"
             "  · right\n    have hi' : i = a.size := by\n      by_contra hne; exact hn ⟨by omega, hm⟩\n    subst hi'\n"
             "    refine ⟨hm, hn', ?_⟩\n    rw [Array.all_eq_true_iff_forall_mem, Refine.forall_mem_array_iff_idx]\n"
             "    intro k hk\n    rw [Array.all_eq_true_iff_forall_mem, Refine.forall_mem_array_iff_idx]\n    intro j hj\n"
             "    simpa using hall k hk j hj"}

ORACLES_MORE = {
    "verina_basic_90": with_lemmas(
        loop([["i", "Nat"], ["mm", "Int"], ["nn", "Int"]], ["0", "-1", "-1"], _INV, "i < a.size ∧ mm = -1", "a.size - i", "(mm, nn)",
             bind("jr", "Int", _PROP,
                  with_lemmas(
                      loop([["j", "Nat"]], ["0"], "j ≤ (a[i]!).size ∧ ∀ j', j' < j → (a[i]!)[j']! ≠ key",
                           "j < (a[i]!).size ∧ (a[i]!)[j]! ≠ key", "(a[i]!).size - j",
                           "if j < (a[i]!).size then (j : Int) else -1", term("j + 1")),
                      [_WIDTH, _INNER_EXIT]),
                  with_lemmas(term("(i + 1, if jr = -1 then -1 else (i : Int), jr)"), [_STEP]))),
        [_EXIT]),
}
