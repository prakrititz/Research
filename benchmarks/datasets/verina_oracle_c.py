r"""Hand-written derivations for Verina tasks, batch C (strings and arrays: builders, flags, searches with helper lemmas)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas


def _string_builder(elem):
    """The string whose j-th character is ``elem(j)`` (``elem`` uses the placeholder J for the index)."""
    return loop([["i", "Nat"], ["acc", "List Char"]], ["0", "[]"],
                f"i ≤ s.length ∧ acc = (List.range i).map (fun j => {elem.replace('J', 'j')})", "i < s.length", "s.length - i",
                "String.mk acc", term(f"(i + 1, acc ++ [{elem.replace('J', 'i')}])"))


def _list_builder(elem, size, name="acc", typ="Array Int", push="push"):
    return loop([["i", "Nat"], [name, typ]], ["0", "#[]"],
                f"i ≤ {size} ∧ {name}.size = i ∧ ∀ jj, jj < i → {name}[jj]! = {elem.replace('J', 'jj')}", f"i < {size}",
                f"{size} - i", name, term(f"(i + 1, {name}.{push} ({elem.replace('J', 'i')}))"))


_ALLSAME = [{"name": "allsame_pairwise",
             "statement": "∀ (l : List Char), (∀ k, k < l.length → l[k]! = l[0]!) → List.Pairwise (· = ·) l",
             "proof": "by intro l h\n  apply List.pairwise_of_forall_mem_list\n  intro a ha b hb\n"
                      "  obtain ⟨i, hi, rfl⟩ := (Refine.mem_iff_idx l a).mp ha\n"
                      "  obtain ⟨j, hj, rfl⟩ := (Refine.mem_iff_idx l b).mp hb\n  rw [h i hi, h j hj]"},
            {"name": "allsame_not",
             "statement": "∀ (l : List Char), ¬ (∀ k, k < l.length → l[k]! = l[0]!) → l ≠ [] ∧ l.any (fun x => decide (x ≠ l[0]!)) = true",
             "proof": "by intro l h\n  push_neg at h\n  obtain ⟨k, hk, hne⟩ := h\n  refine ⟨?_, ?_⟩\n"
                      "  · intro h0; subst h0; simp at hk\n"
                      "  · rw [List.any_eq_true]\n    refine ⟨l[k]!, ?_, by simpa using hne⟩\n    rw [getElem!_pos l k hk]; exact List.getElem_mem hk"}]

ORACLES_MORE = {
    "verina_basic_16": _string_builder("(if s.toList[J]! = oldChar then newChar else s.toList[J]!)"),
    "verina_basic_17": _string_builder("(if isUpperCase s.toList[J]! then shift32 s.toList[J]! else s.toList[J]!)"),
    "verina_basic_31": _string_builder("(if isLowerCase s.toList[J]! then shiftMinus32 s.toList[J]! else s.toList[J]!)"),
    "verina_basic_36": _string_builder("(if isSpaceCommaDot s.toList[J]! then ':' else s.toList[J]!)"),
    "verina_basic_21": loop([["i", "Nat"], ["f", "Bool"]], ["0", "false"],
                            "i ≤ main.length + 1 ∧ (f = true ↔ ∃ k, k < i ∧ k + sub.length ≤ main.length ∧ sub = (main.drop k).take sub.length)",
                            "i < main.length + 1", "main.length + 1 - i", "f",
                            term("(i + 1, f || decide (i + sub.length ≤ main.length ∧ sub = (main.drop i).take sub.length))")),
    "verina_basic_38": with_lemmas(
        loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
             "i ≤ s.toList.length ∧ (ok = true ↔ ∀ k, k < i → s.toList[k]! = s.toList[0]!)", "i < s.toList.length",
             "s.toList.length - i", "ok", term("(i + 1, ok && decide (s.toList[i]! = s.toList[0]!))")), _ALLSAME),
    "verina_basic_3": with_lemmas(
        term("decide (n % 11 = 0)"),
        [{"name": "div11_ok",
          "statement": "∀ (n : Int), (decide (n % 11 = 0) = true → ∃ k : Int, n = 11 * k) ∧ (¬ decide (n % 11 = 0) = true → ∀ k : Int, ¬ n = 11 * k)",
          "proof": "by intro n\n  constructor\n  · intro h\n    have : n % 11 = 0 := by simpa using h\n    exact ⟨n / 11, by omega⟩\n"
                   "  · intro h k hk\n    apply h\n    simp\n    omega"}]),
    "verina_basic_66": with_lemmas(
        term("decide (x % 2 = 0)"),
        [{"name": "even_ok", "statement": "∀ (x : Int), (decide (x % 2 = 0) = true ↔ ∃ k : Int, x = 2 * k)",
          "proof": "by intro x\n  constructor\n  · intro h\n    have : x % 2 = 0 := by simpa using h\n    exact ⟨x / 2, by omega⟩\n"
                   "  · rintro ⟨k, rfl⟩\n    simp <;> omega"}]),
    "verina_basic_48": with_lemmas(
        term("decide (Nat.sqrt n * Nat.sqrt n = n)"),
        [{"name": "square_ok", "statement": "∀ (n : Nat), (decide (Nat.sqrt n * Nat.sqrt n = n) = true ↔ ∃ i : Nat, i * i = n)",
          "proof": "by intro n\n  constructor\n  · intro h\n    exact ⟨Nat.sqrt n, by simpa using h⟩\n"
                   "  · rintro ⟨i, rfl⟩\n    simp [Nat.sqrt_eq]"}]),
    "verina_basic_88": _list_builder("xs[J]!", "xs.length"),
    "verina_basic_82": loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                            "i ≤ a.size - 1 ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = a[jj + 1]!", "i < a.size - 1", "a.size - 1 - i",
                            "acc", term("(i + 1, acc.push a[i + 1]!)")),
    "verina_basic_72": term("a.push b"),
    "verina_basic_97": term("a.set! j 60"),
    "verina_basic_103": term("(a.set! 4 (a[4]! + 3)).set! 7 516"),
    "verina_basic_77": term("arr.set! index1 ((arr[index1]!).set! index2 val)"),
    "verina_basic_95": term("(arr.set! (Int.toNat i) arr[Int.toNat j]!).set! (Int.toNat j) arr[Int.toNat i]!"),
    "verina_basic_32": term("(a.set! 0 a[a.size - 1]!).set! (a.size - 1) a[0]!"),
    "verina_basic_81": with_lemmas(
        cases("y = 0", term("(Int.ofNat x, 0)"), term("(Int.ofNat (x % y), Int.ofNat (x / y))")),
        [{"name": "divmod_ok",
          "statement": "∀ (x y : Nat), y ≠ 0 → (Int.ofNat (x / y) * Int.ofNat y + Int.ofNat (x % y) = Int.ofNat x ∧ "
                       "(0 ≤ Int.ofNat (x % y) ∧ Int.ofNat (x % y) < Int.ofNat y) ∧ 0 ≤ Int.ofNat (x / y))",
          "proof": "by intro x y hy\n  have h1 : x / y * y + x % y = x := Nat.div_add_mod' x y\n  have h2 : x % y < y := Nat.mod_lt x (Nat.pos_of_ne_zero hy)\n"
                   "  refine ⟨?_, ⟨Int.ofNat_nonneg _, Int.ofNat_lt.mpr h2⟩, Int.ofNat_nonneg _⟩\n"
                   "  have h3 : (((x / y * y + x % y : Nat)) : Int) = (x : Int) := congrArg (fun n : Nat => (n : Int)) h1\n"
                   "  simpa [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul] using h3"}]),
}
