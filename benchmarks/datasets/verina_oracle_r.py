r"""Hand-written derivations for Verina tasks, batch R (advanced: arithmetic on digit lists)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_L2N = {
    "name": "l2n",
    "statement": "∀ (l : List Nat), listToNat l = Nat.ofDigits 10 l",
    "proof": "by intro l\n  induction l with\n  | nil => simp [listToNat, Nat.ofDigits]\n"
             "  | cons a t ih => simp [listToNat, Nat.ofDigits_cons, ih]"}
_GLCC = {
    "name": "gl_cc",
    "statement": "∀ (a b : Nat) (t : List Nat), (a :: b :: t).getLast! = (b :: t).getLast!",
    "proof": "by intro a b t\n  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_cons_cons]"}
_LASTPOS = {
    "name": "last_pos",
    "statement": "∀ (l : List Nat), l ≠ [] → l.getLast! ≠ 0 → 0 < listToNat l",
    "proof": "by intro l\n  induction l with\n  | nil => intro h; exact absurd rfl h\n  | cons a t ih =>\n    intro _ hl\n    cases t with\n"
             "    | nil => simp [listToNat] at hl ⊢; omega\n    | cons b t' =>\n"
             "      have hl' : (b :: t').getLast! ≠ 0 := by rw [gl_cc] at hl; exact hl\n"
             "      have := ih (by simp) hl'\n      simp only [listToNat] at this ⊢; omega"}
_DLAST = {
    "name": "digits_last",
    "statement": "∀ (s : Nat), s ≠ 0 → (Nat.digits 10 s).getLast! ≠ 0",
    "proof": "by intro s hs\n  have h := Nat.getLast_digit_ne_zero 10 hs\n  have hne : Nat.digits 10 s ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hs\n"
             "  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getLast_of_ne_nil hne]\n  simpa using h"}
_E5 = "if listToNat l1 + listToNat l2 = 0 then [0] else Nat.digits 10 (listToNat l1 + listToNat l2)"
_ADD5 = {
    "name": "add5",
    "statement": f"∀ (l1 l2 : List Nat) (h : addTwoNumbers_precond l1 l2), addTwoNumbers_postcond l1 l2 ({_E5}) h",
    "proof": "by intro l1 l2 h\n  obtain ⟨hl1, hl2, hd1, hd2, hg1, hg2⟩ := h\n  unfold addTwoNumbers_postcond\n"
             "  by_cases hz : listToNat l1 + listToNat l2 = 0\n  · rw [if_pos hz]\n"
             "    refine ⟨by simp [listToNat, hz], by simp, Or.inr ⟨?_, ?_, rfl⟩⟩\n"
             "    · rcases hg1 with hg | hg\n      · have := last_pos l1 (by intro e; simp [e] at hl1) hg; omega\n      · exact hg\n"
             "    · rcases hg2 with hg | hg\n      · have := last_pos l2 (by intro e; simp [e] at hl2) hg; omega\n      · exact hg\n"
             "  · rw [if_neg hz]\n    refine ⟨?_, fun d hd => Nat.digits_lt_base (by norm_num) hd, Or.inl (digits_last _ hz)⟩\n"
             "    rw [l2n (Nat.digits 10 _), Nat.ofDigits_digits]"}

ORACLES_MORE = {
    "verina_advanced_5": with_lemmas(term(f"({_E5})"), [_L2N, _GLCC, _LASTPOS, _DLAST, _ADD5]),
}
