r"""Hand-written derivations for Verina tasks, batch B (the basic family: arrays, strings, searches, small arithmetic)."""
from benchmarks.datasets.derivation_dsl import bind, cases, loop, term, with_lemmas


def _builder(arr, elem, size="a.size", src="a"):
    """acc.push (elem i): the array of ``elem k`` for k < i; ``elem`` uses the loop variable ``i``."""
    return loop([["i", "Nat"], ["acc", "Array Int"]], ["0", "#[]"],
                f"i ≤ {size} ∧ acc.size = i ∧ ∀ jj, jj < i → acc[jj]! = {elem.replace('IDX', 'jj')}", f"i < {size}", f"{size} - i", "acc",
                term(f"(i + 1, acc.push ({elem.replace('IDX', 'i')}))"))


ORACLES_MORE = {
    "verina_basic_101": term("x * 3"),
    "verina_basic_98": term("x * 3"),
    "verina_basic_99": term("x * 3"),
    "verina_basic_59": term("(2 * x, 4 * x)"),
    "verina_basic_6": cases("a ≤ b ∧ a ≤ c", term("a"), cases("b ≤ a ∧ b ≤ c", term("b"), term("c"))),
    "verina_basic_76": cases("x < y", term("x"), term("y")),
    "verina_basic_8": cases("a ≤ b", term("a"), term("b")),
    "verina_basic_78": term("(x + y, x - y)"),
    "verina_basic_91": with_lemmas(term("(Y, X)"), [{"name": "swap_ok", "statement": "∀ (X Y : Int) (h : Swap_precond X Y), Swap_postcond X Y (Y, X) h",
          "proof": "by intro X Y h\n  unfold Swap_postcond\n  refine ⟨rfl, rfl, fun hne => ⟨fun h2 => hne h2.symm, fun h2 => hne h2⟩⟩"}]),
    "verina_basic_92": with_lemmas(term("(Y, X)"), [{"name": "swaparithmetic_ok", "statement": "∀ (X Y : Int) (h : SwapArithmetic_precond X Y), SwapArithmetic_postcond X Y (Y, X) h",
          "proof": "by intro X Y h\n  unfold SwapArithmetic_postcond\n  refine ⟨rfl, rfl, fun hne => ⟨fun h2 => hne h2.symm, fun h2 => hne h2⟩⟩"}]),
    "verina_basic_93": with_lemmas(term("(Y, X)"), [{"name": "swapbitvectors_ok", "statement": "∀ (X Y : UInt8) (h : SwapBitvectors_precond X Y), SwapBitvectors_postcond X Y (Y, X) h",
          "proof": "by intro X Y h\n  unfold SwapBitvectors_postcond\n  refine ⟨rfl, rfl, fun hne => ⟨fun h2 => hne h2.symm, fun h2 => hne h2⟩⟩"}]),
    "verina_basic_96": with_lemmas(term("(Y, X)"), [{"name": "swapsimultaneous_ok", "statement": "∀ (X Y : Int) (h : SwapSimultaneous_precond X Y), SwapSimultaneous_postcond X Y (Y, X) h",
          "proof": "by intro X Y h\n  unfold SwapSimultaneous_postcond\n  refine ⟨rfl, rfl, fun hne => ⟨fun h2 => hne h2.symm, fun h2 => hne h2⟩⟩"}]),
    "verina_basic_94": term("s"),
    "verina_basic_58": _builder("s", "2 * s[IDX]!", "s.size"),
    "verina_basic_85": _builder("a", "a[a.size - 1 - IDX]!"),
    "verina_basic_84": _builder("arr", "(if arr[IDX]! > k then -1 else arr[IDX]!)", "arr.size"),
    "verina_basic_83": _builder("a", "(if IDX < a.size then a[IDX]! else b[IDX - a.size]!)", "a.size + b.size"),
    "verina_basic_65": loop([["r", "Nat"]], ["0"], "r * r ≤ N", "(r + 1) * (r + 1) ≤ N", "N - r", "r", term("r + 1")),
    "verina_basic_67": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                            "i ≤ x.length ∧ (ok = true ↔ ∀ k, k < i → x[k]! = x[x.length - k - 1]!)", "i < x.length",
                            "x.length - i", "ok", term("(i + 1, ok && decide (x[i]! = x[x.length - i - 1]!))")),
    "verina_basic_73": loop([["i", "Nat"], ["ok", "Bool"]], ["0", "true"],
                            "i ≤ s.toList.length ∧ (ok = true ↔ ∀ k, k < i → (s.toList[k]! = p.toList[k]! ∨ p.toList[k]! = '?'))",
                            "i < s.toList.length", "s.toList.length - i", "ok",
                            term("(i + 1, ok && decide (s.toList[i]! = p.toList[i]! ∨ p.toList[i]! = '?'))")),
    "verina_basic_68": loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ i, i < n → a[i]! ≠ e", "n < a.size ∧ a[n]! ≠ e",
                            "a.size - n", "n", term("n + 1")),
    "verina_basic_62": loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ i, i < n → a[i]! ≠ key", "n < a.size ∧ a[n]! ≠ key",
                            "a.size - n", "if n < a.size then (n : Int) else -1", term("n + 1")),
    "verina_basic_37": loop([["n", "Nat"]], ["0"], "n ≤ arr.size ∧ ∀ i, i < n → arr[i]! ≠ target", "n < arr.size ∧ arr[n]! ≠ target",
                            "arr.size - n", "if n < arr.size then (n : Int) else -1", term("n + 1")),
    "verina_basic_70": loop([["n", "Nat"]], ["0"], "n ≤ a.size ∧ ∀ k, k < n → ¬ P a[k]!", "n < a.size ∧ ¬ P a[n]!",
                            "a.size - n", "n", term("n + 1")),
    "verina_basic_80": term("decide (count_occurrences a key = 1)"),
    "verina_basic_20": term("arr.toList.eraseDups.foldl (· * ·) 1"),
    "verina_basic_42": term("List.length (List.filter isDigit s.toList)"),
    "verina_basic_18": term("List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n)))"),
    "verina_basic_28": term("(List.range' 2 (n - 2)).all (fun k => n % k != 0)"),
    "verina_basic_15": loop([["i", "Nat"], ["f", "Bool"]], ["0", "false"],
                            "i ≤ a.size - 1 ∧ (f = true ↔ ∃ k, k < i ∧ a[k]! + 1 = a[k + 1]!)", "i < a.size - 1", "a.size - 1 - i", "f",
                            term("(i + 1, f || decide (a[i]! + 1 = a[i + 1]!))")),
    "verina_basic_14": term("s.toList.any (fun c => c == 'z' || c == 'Z')"),
}
