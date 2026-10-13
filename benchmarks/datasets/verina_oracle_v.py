r"""Hand-written derivations for Verina tasks, batch V (advanced: lexicographic minimum)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_FM = {"name": "fold_minkey",
       "statement": "∀ {α β : Type} [LinearOrder β] (f : α → β) (L : List α) (b : α), "
                    "(L.foldl (fun best y => if f y < f best then y else best) b = b ∨ L.foldl (fun best y => if f y < f best then y else best) b ∈ L) ∧ "
                    "f (L.foldl (fun best y => if f y < f best then y else best) b) ≤ f b ∧ "
                    "∀ y ∈ L, f (L.foldl (fun best y => if f y < f best then y else best) b) ≤ f y",
       "proof": "by\n  intro α β _ f L\n  induction L with\n  | nil => intro b; simp\n  | cons a t ih =>\n    intro b\n    simp only [List.foldl_cons]\n    by_cases hlt : f a < f b\n    · rw [if_pos hlt]\n      obtain ⟨h1, h2, h3⟩ := ih a\n      refine ⟨?_, le_trans h2 (le_of_lt hlt), ?_⟩\n      · rcases h1 with h | h\n        · right; rw [h]; exact List.mem_cons_self\n        · right; exact List.mem_cons_of_mem a h\n      · intro x hx\n        rcases List.mem_cons.mp hx with rfl | hx'\n        · exact h2\n        · exact h3 x hx'\n    · rw [if_neg hlt]\n      obtain ⟨h1, h2, h3⟩ := ih b\n      refine ⟨?_, h2, ?_⟩\n      · rcases h1 with h | h\n        · left; exact h\n        · right; exact List.mem_cons_of_mem a h\n      · intro x hx\n        rcases List.mem_cons.mp hx with rfl | hx'\n        · exact le_trans h2 (not_lt.mp hlt)\n        · exact h3 x hx'\n"}
_MIN71 = {"name": "min71",
          "statement": "∀ (targets : List String), (let res := (match targets with | [] => \"\" | b :: t => (b :: t).foldl "
                       "(fun best y => if toLex (y.length, y) < toLex (best.length, best) then y else best) b); "
                       "(res = \"\" ∧ targets = []) ∨ (res ∈ targets ∧ ∀ r ∈ targets, r.length > res.length ∨ (r.length = res.length ∧ res ≤ r)))",
          "proof": "by\n  intro targets\n  cases targets with\n  | nil => dsimp only; left; exact ⟨rfl, rfl⟩\n  | cons b t =>\n    dsimp only\n    right\n    obtain ⟨h1, h2, h3⟩ := fold_minkey (fun s : String => toLex (s.length, s)) (b :: t) b\n    generalize (b :: t).foldl (fun best y => if toLex (y.length, y) < toLex (best.length, best) then y else best) b = r at h1 h2 h3\n    refine ⟨?_, ?_⟩\n    · rcases h1 with h | h\n      · rw [h]; exact List.mem_cons_self\n      · exact h\n    · intro y hy\n      have := h3 y hy\n      rw [Prod.Lex.le_iff] at this\n      simp only [ofLex_toLex] at this\n      rcases this with h | ⟨h, h'⟩\n      · left; exact h\n      · right; exact ⟨h.symm, h'⟩\n"}
_LETS71 = 'let chars := s.data; let substrings := (List.range chars.length).flatMap (fun i => (List.range (chars.length - i + 1)).map (fun len => chars.drop i |>.take len)); let isBeautiful := fun sub => countOnes sub = k; let beautiful := substrings.filter (fun sub => isBeautiful sub); let targets := beautiful.map (·.asString) |>.filter (fun s => s ≠ ""); '
_FOLD71 = 'match targets with | [] => "" | b :: t => (b :: t).foldl (fun best y => if toLex (y.length, y) < toLex (best.length, best) then y else best) b'
_E71 = _LETS71 + _FOLD71
_L71 = {"name": "short71",
        "statement": "∀ (s : String) (k : Nat) (h : shortestBeautifulSubstring_precond s k), shortestBeautifulSubstring_postcond s k (" + _E71 + ") h",
        "proof": "by intro s k h\n  unfold shortestBeautifulSubstring_postcond\n  intro chars substrings isBeautiful beautiful targets\n  exact min71 targets"}

ORACLES_MORE = {
    "verina_advanced_71": with_lemmas(term("(" + _E71 + ")"), [_FM, _MIN71, _L71]),
}
