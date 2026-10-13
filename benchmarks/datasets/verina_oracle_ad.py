r"""Hand-written derivations for Verina tasks, batch AD (advanced: run-length encoding with a reversed stack of runs)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas

_SMA = {"name": "str_mk_append", "statement": "∀ (a b : List Char), String.mk (a ++ b) = String.mk a ++ String.mk b",
        "proof": 'by\n  intro a b\n  apply String.ext\n  rw [String.toList_append]\n  simp only [Refine.string_toList_mk]\n'}
_DA = {"name": "dec_append", "statement": "∀ (xs ys : List (Char × Nat)), decodeRLE (xs ++ ys) = decodeRLE xs ++ decodeRLE ys",
       "proof": 'by\n  intro xs ys\n  induction xs with\n  | nil => simp [decodeRLE]\n  | cons p t ih =>\n    obtain ⟨c, n⟩ := p\n    simp only [List.cons_append, decodeRLE, ih]\n    rw [String.append_assoc]\n'}
_DS = {"name": "dec_single", "statement": "∀ (c : Char) (n : Nat), decodeRLE [(c, n)] = String.mk (List.replicate n c)",
       "proof": 'by\n  intro c n\n  simp [decodeRLE]\n'}
_DR = {"name": "dec_rev_cons", "statement": "∀ (c : Char) (n : Nat) (rest : List (Char × Nat)), "
                                          "decodeRLE ((c, n) :: rest).reverse = decodeRLE rest.reverse ++ String.mk (List.replicate n c)",
       "proof": 'by\n  intro c n rest\n  rw [List.reverse_cons, dec_append, dec_single]\n'}
_INV = 'i ≤ cs.length ∧ decodeRLE acc.reverse = String.mk (cs.take i) ∧ (∀ p ∈ acc, 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) acc'
_EXPR = '(if (acc.head?.map Prod.fst) = some cs[i]! then (cs[i]!, (acc.headD (cs[i]!, 0)).2 + 1) :: acc.tail else (cs[i]!, 1) :: acc)'
_STEP = {"name": "rle_step2",
         "statement": "∀ (cs : List Char) (i : Nat) (acc : List (Char × Nat)), i < cs.length → (" + _INV + ") → "
                      "(i + 1 ≤ cs.length ∧ decodeRLE " + _EXPR + ".reverse = String.mk (cs.take (i + 1)) ∧ "
                      "(∀ p ∈ " + _EXPR + ", 0 < p.2) ∧ List.IsChain (fun a b => a.1 ≠ b.1) " + _EXPR + ")",
         "proof": "by\n  intro cs i acc hi hinv\n  obtain ⟨_, hdec, hpos, hch⟩ := hinv\n  have htake : String.mk (cs.take (i + 1)) = String.mk (cs.take i) ++ String.mk [cs[i]!] := by\n    rw [Refine.take_succ_bang cs i hi, str_mk_append]\n  refine ⟨by omega, ?_⟩\n  rw [htake, ← hdec]\n  generalize cs[i]! = c\n  cases acc with\n  | nil =>\n    simp [decodeRLE]\n  | cons p rest =>\n    obtain ⟨c', n⟩ := p\n    split_ifs with h\n    · have hc : c' = c := by simpa using h\n      subst hc\n      simp only [List.headD_cons, List.tail_cons]\n      refine ⟨?_, ?_, ?_⟩\n      · rw [dec_rev_cons, dec_rev_cons, List.replicate_succ', str_mk_append, String.append_assoc]\n      · intro q hq\n        rcases List.mem_cons.mp hq with rfl | hq'\n        · simp\n        · exact hpos q (List.mem_cons_of_mem _ hq')\n      · cases rest with\n        | nil => simp\n        | cons r rs =>\n          rw [List.isChain_cons_cons] at hch ⊢\n          exact hch\n    · have hc : c' ≠ c := fun e => h (by simp [e])\n      refine ⟨?_, ?_, ?_⟩\n      · rw [dec_rev_cons, dec_rev_cons]; simp [List.replicate]\n      · intro q hq\n        rcases List.mem_cons.mp hq with rfl | hq'\n        · simp\n        · exact hpos q hq'\n      · rw [List.isChain_cons_cons]\n        exact ⟨fun e => hc e.symm, hch⟩\n"}
_EXIT = {"name": "exit67",
         "statement": "∀ (s : String) (h : runLengthEncode_precond s) (i : Nat) (acc : List (Char × Nat)), "
                      "(i ≤ s.toList.length ∧ decodeRLE acc.reverse = String.mk (s.toList.take i) ∧ (∀ p ∈ acc, 0 < p.2) ∧ "
                      "List.IsChain (fun a b => a.1 ≠ b.1) acc) → ¬ i < s.toList.length → runLengthEncode_postcond s acc.reverse h",
         "proof": "by\n  intro s h i acc hinv hn\n  obtain ⟨hi, hdec, hpos, hch⟩ := hinv\n  unfold runLengthEncode_postcond\n  have hi' : i = s.toList.length := by omega\n  subst hi'\n  rw [List.take_of_length_le (le_refl _)] at hdec\n  refine ⟨?_, ?_, ?_⟩\n  · intro p hp\n    exact hpos p (List.mem_reverse.mp hp)\n  · intro k hk\n    have hchr : List.IsChain (fun a b => a.1 ≠ b.1) acc.reverse := by\n      rw [List.isChain_reverse]\n      refine hch.imp ?_\n      intro a b h e\n      exact h e.symm\n    have hk' : k + 1 < acc.reverse.length := by omega\n    have := List.isChain_iff_getElem.mp hchr k hk'\n    rw [getElem!_pos acc.reverse k (by omega), getElem!_pos acc.reverse (k + 1) hk']\n    exact this\n  · rw [hdec]\n    apply String.ext\n    simp only [Refine.string_toList_mk]\n"}

_INV_S = _INV.replace("cs.length", "s.toList.length").replace("cs.take", "s.toList.take")
_EXPR_S = _EXPR.replace("cs[i]!", "s.toList[i]!")

ORACLES_MORE = {
    "verina_advanced_67": with_lemmas(
        loop([["i", "Nat"], ["acc", "List (Char × Nat)"]], ["0", "[]"], _INV_S, "i < s.toList.length", "s.toList.length - i", "acc.reverse",
             term("(i + 1, " + _EXPR_S + ")")),
        [_SMA, _DA, _DS, _DR, _STEP, _EXIT]),
}
